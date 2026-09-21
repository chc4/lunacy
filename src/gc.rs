#![allow(unused_parens)]
use std::ops::Deref;
use std::hash::Hash;
use std::rc::Rc;
use std::cell::{Cell, UnsafeCell};
use std::marker::PhantomData;
use std::collections::BTreeMap;
use std::sync::atomic::{Ordering, AtomicBool, AtomicPtr};
use crate::vm::{Tc, LValue, LBoxed, LCanon, LClosure, NClosure, Table, Upvalue};
use crate::vm::FVec;
use crate::{TLCell, TlcOwner, Owner};
use indexmap::IndexMap;
use crate::debug;

pub trait Mark {
    fn mark(&self, owner: &Owner);
}

impl<'src, 'intern> Mark for LValue<'src, 'intern> {
    fn mark(&self, owner: &Owner) {
        match self {
            LValue::Nil | LValue::Bool(_) | LValue::Number(_) => { },
            LValue::Table(t) => t.mark(owner),
            LValue::InternedString(_) => { },
            LValue::OwnedString(s) => s.mark(owner),
            LValue::LClosure(c) => c.mark(owner),
            LValue::NClosure(c) => c.mark(owner),
        }
    }
}

impl<'src, 'intern> Mark for LBoxed<'src, 'intern> {
    // Trace through the decoded value; `LValue::mark` no-ops the non-cell arms.
    fn mark(&self, owner: &Owner) {
        self.unbox().mark(owner);
    }
}

impl<'src, 'intern> Mark for LCanon<'src, 'intern> {
    // A canonical value may wrap a table/closure (held by identity), so trace the
    // underlying boxed value.
    fn mark(&self, owner: &Owner) {
        self.boxed().mark(owner);
    }
}

// All types are Mark by default
impl<T> Mark for T {
    default fn mark(&self, _owner: &Owner) {
        if const { std::intrinsics::needs_drop::<T>() } {
            panic!("default Mark for non-trivial drop {}", const { std::intrinsics::type_name::<T>() })
        }
    }
}

impl<T> Mark for Tc<T> {
    fn mark(&self, owner: &Owner) {
        self.0.mark(owner)
    }
}

impl<T: Mark> Mark for TLCell<TlcOwner, T> {
    fn mark(&self, owner: &Owner) {
        self.ro(owner).mark(owner)
    }
}

impl<T> Mark for Rc<T> {
    fn mark(&self, owner: &Owner) {
        self.deref().mark(owner)
    }
}

impl<T> Mark for Box<T> {
    fn mark(&self, owner: &Owner) {
        self.deref().mark(owner)
    }
}

impl Mark for Box<dyn Mark> {
    fn mark(&self, owner: &Owner) {
        self.deref().mark(owner)
    }
}

impl<'src, 'intern> Mark for Table<'src, 'intern> {
    fn mark(&self, owner: &Owner) {
        for item in self.array.iter() {
            item.mark(owner);
        }
        self.hash.mark(owner);
    }
}

impl<'src, 'intern> Mark for LClosure<'src, 'intern> {
    fn mark(&self, owner: &Owner) {
        for upval in self.upvalues.iter() {
            upval.mark(owner);
        }
    }
}

impl Mark for NClosure {
    fn mark(&self, _owner: &Owner) { }
}

impl<'src, 'intern> Mark for Upvalue<'src, 'intern> {
    fn mark(&self, owner: &Owner) {
        if let Upvalue::Closed(o) = self {
            o.mark(owner)
        }
    }
}

impl<K: Mark, V: Mark, S> Mark for IndexMap<K, V, S> {
    fn mark(&self, owner: &Owner) {
        for (k, v) in self {
            k.mark(owner);
            v.mark(owner);
        }
    }
}

impl<T: Mark> Mark for Vec<T> {
    fn mark(&self, owner: &Owner) {
        for item in self.iter() {
            item.mark(owner);
        }
    }
}

// Note [Incremental GC]
// ~~~~~~~~~~~~~~~~~~~~~~
// A tricolor mark/sweep collector. Each object is white (unreached), gray (reached but its
// children are not yet scanned — on the `gray` worklist), or black (reached and scanned).
// The strong invariant is that a black object never points directly at a white one.
// Marking is incremental: each safepoint shades the roots then scans a bounded budget of
// gray objects, so the mark phase spreads across many safepoints instead of one pause. A
// cycle starts once live `total_bytes` crosses `threshold` (re-armed to 2x live after each
// cycle). When the worklist empties, `finish` runs the atomic tail with the mutator
// stopped: fold in grayagain (see Note [Write barriers]), re-scan the roots, drain, sweep.
// Sweep is atomic, so one white color suffices: objects allocated mid-cycle are white and
// cannot be swept before the next completed mark. At cycle end every survivor is black, so
// `sweep_free` flips the white/black interpretation (one global toggle) instead of
// recoloring each survivor.
//
// Note [Write barriers]
// ~~~~~~~~~~~~~~~~~~~~~~
// Between increments the mutator can create a black->white edge, which would let the
// collector free a reachable object. Two barriers preserve the invariant, split as in Lua:
//   * non-tables: a forward (Dijkstra) barrier (`Gc::write_barrier`) shades the written
//     value, so the container stays black and the frontier advances incrementally.
//   * tables: a backward barrier (`Gc::backward_barrier`, Lua's `barrierback`) reverts the
//     mutated table to gray onto `grayagain`, re-scanned once in the atomic `finish`.
//     Tables are mutated often, so this avoids shading every write, paying an atomic
//     re-scan of the mutated tables instead.
// Neither barrier re-enters the incremental `gray` worklist, so a hot mutation loop cannot
// keep the collector marking forever. Both are self-gating: nothing is black while idle,
// so the fast path is one load and branch.
//
// Note [GC roots]
// ~~~~~~~~~~~~~~~
// The roots are the interpreter `RunState` (whose value stack covers every Lua frame) and
// the JIT `Specializer`, plus the `Heap::root` set.
//
// A collection runs only through a `GcCtx` token, minted inside `Heap::rooted`/`root_scope`
// and cleared on scope exit, so roots are never read after a run ends. `RunState` moves between
// the interpreter and `Specializer::run`, so the token republishes the live `&state`/`&spec` at
// each safepoint rather than storing one pointer that would dangle across the move.
//
// All live objects must be reachable through one of these roots before a GC safepoint, or else
// the object may be collected and freed.
//
// Note [Scoped heap]
// ~~~~~~~~~~~~~~~~~~
// `HEAP` is a `const`-initialized thread-local, so `hp()` is a plain TLS load and two threads
// never share GC state. The `TlcOwner` cell owner is unique per thread (a second `Owner::new`
// panics), so a thread hosts at most one VM at a time.
//
// A VM epoch is one `Vm::scope` call. The heap outlives any single epoch, yet its objects,
// roots, and worklists all borrow that epoch's `'src`/`'intern` and so must be freed before
// those arenas are. `Vm::scope` guarantees this: it hands the body a `Scoped<'gc>` that views
// the VM and arena at a fresh invariant `'gc`, pinned strictly shorter than `'src`/`'intern`
// (see the SAFETY note on `Vm::scope`). Every GC value the body can reach is then `<'gc,'gc>`,
// which the higher-ranked `for<'gc>` bound keeps from escaping the body — so on exit the heap
// is unreachable and `Heap::reset` can free all of it. Scopes are not re-entrant, since an
// inner reset would free the outer epoch's live objects. The interpreter entry points
// (`Vm::run`, `Vm::global_env`) are crate-private and reachable only through `Scoped`, so a run
// always sits inside a scope.
//
// "White" and "black" are the two values in {0,1}; which one currently means white
// (unreached) flips each cycle in `sweep_free`, so all survivors become white again with a
// single toggle instead of a write per live object. GRAY is the stable third value and is
// never a flip target.
const GRAY: u8 = 2;
#[inline]
fn white() -> u8 { unsafe { (*hp()).current_white } }
#[inline]
fn black() -> u8 { white() ^ 1 }

/// Gray objects scanned per incremental step during normal operation.
const STEP_BUDGET: usize = 512;
/// Floor on the cycle-trigger threshold, so a tiny live set doesn't cause thrashing.
const MIN_THRESHOLD: usize = 256 * 1024;
/// Live heap that triggers the first collection cycle.
const INITIAL_THRESHOLD: usize = 1024 * 1024;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Phase {
    Idle,
    Mark,
}

// TODO: const marker trait for trivial drop, since we don't run finalizers?
#[derive(Eq, PartialEq)]
#[repr(transparent)]
pub struct Gc<T: ?Sized> {
    ptr: core::ptr::NonNull<GcInner<T>>,
}

impl<T> Gc<T> {
    pub fn as_ptr(&self) -> *const T {
        unsafe { &self.ptr.as_ref().val }
    }

    /// The raw address of the `GcInner` allocation.
    #[inline(always)]
    pub fn to_addr(&self) -> u64 {
        self.ptr.as_ptr() as u64
    }

    /// Reconstruct a `Gc<T>` from an address produced by [`Gc::to_addr`].
    /// SAFETY: `addr` must be an address returned by `to_addr` for a `Gc<T>`
    /// of the exact same `T` that is still live.
    #[inline(always)]
    pub unsafe fn from_addr(addr: u64) -> Self {
        Self { ptr: core::ptr::NonNull::new_unchecked(addr as *mut GcInner<T>) }
    }

    pub fn new(val: T) -> Self where T: CellKind {
        let heap = hp();
        let size = core::mem::size_of::<GcInner<T>>();
        let mut top = unsafe { (*heap).top.load(Ordering::Acquire) };
        let inner = GcInner {
            kind: <T as CellKind>::cell_kind(),
            next: AtomicPtr::new(top),
            // Born white; swept next cycle unless reached. See Note [Incremental GC].
            color: Cell::new(white()),
            size,
            #[cfg(feature = "gc_sanitize")]
            finalize: |ptr| unsafe {
                let ptr = ptr.cast::<GcInner<T>>();
                (*ptr).alive.store(false, Ordering::Release)
            },
            #[cfg(feature = "gc_sanitize")]
            alive: AtomicBool::new(true),

            #[cfg(not(feature = "gc_sanitize"))]
            finalize: |ptr| unsafe { drop(Box::from_raw(ptr.cast::<GcInner<T>>())) },
            val
        };
        let ptr = Box::leak(Box::new(inner));
        loop {
            // Try to put ourself as the new top
            let erased: *mut GcInner<()> = unsafe { core::mem::transmute(ptr as *mut _) };
            match unsafe { (*heap).top.compare_exchange(top, erased, Ordering::Acquire, Ordering::Relaxed) } {
                Ok(_) => {
                    // We were able to swap ourself as the top, which means our next pointer is
                    // correct.
                    break;
                },
                Err(new_top) => {
                    // We failed to set ourself as the top, which means something else did. Update
                    // our next pointer and try again.
                    ptr.next.store(new_top, Ordering::Release);
                    top = new_top;
                    continue;
                },
            }

        }
        // Only accounts for the allocation; stepping happens at safepoints, which have the
        // roots. See Note [GC roots].
        unsafe { (*heap).total_bytes += size; }
        Self { ptr: core::ptr::NonNull::new(ptr as _).unwrap() }
    }

    /// True if this object has been fully scanned this cycle (black).
    #[inline]
    pub fn is_black(&self) -> bool {
        unsafe { (*self.ptr.as_ptr()).color.get() == black() }
    }

    /// Forward barrier: shade `value` when storing it into this (black) object, so the
    /// container may stay black. See Note [Write barriers].
    #[inline]
    pub fn write_barrier<V: Mark>(&self, value: &V, owner: &Owner) {
        if self.is_black() {
            value.mark(owner);
        }
    }

    /// Backward barrier for tables: revert this (black) object to gray onto `grayagain` for
    /// a later atomic re-scan. See Note [Write barriers].
    #[inline]
    pub fn backward_barrier(&self) {
        let inner = self.ptr.as_ptr();
        unsafe {
            if (*inner).color.get() == black() {
                (*inner).color.set(GRAY);
                push_grayagain(inner);
            }
        }
    }
}

// Always clonable
impl<T> core::clone::Clone for Gc<T> {
    fn clone(&self) -> Self {
        Self { ptr: self.ptr.clone() }
    }
}

impl<T> core::fmt::Debug for Gc<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "gc({:p})", self.as_ptr())
    }
}

// `Gc` has no `DerefMut`: it is `Clone`, so several handles can point at one cell
// and a `&mut` through one could alias another. Mutate through a cell + `Owner`,
// which serializes access.
impl<T> Deref for Gc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        #[cfg(feature = "gc_sanitize")]
        unsafe { assert!(self.ptr.as_ref().alive.load(Ordering::Acquire), "value is dead") };
        unsafe { &self.ptr.as_ref().val }
    }
}

impl<T> Hash for Gc<T> {
    default fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_usize(self.ptr.as_ptr() as usize)
    }
}

impl<T: Hash> Hash for Gc<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        unsafe { (*self.ptr.as_ptr()).val.hash(state) }
    }
}

impl<T> Mark for Gc<T> {
    /// Shade this object: white -> gray, enqueued on the worklist. Does not recurse; the
    /// worklist drives scanning, one level per gray object. See Note [Incremental GC].
    fn mark(&self, _owner: &Owner) {
        let inner = self.ptr.as_ptr();
        unsafe {
            if (*inner).color.get() == white() {
                (*inner).color.set(GRAY);
                push_gray(inner);
            }
        }
    }
}

/// `kind` is the cell-type tag read at offset 0 by NuN-boxing (`read_cell_kind`),
/// so it stays first under `#[repr(C)]`; `vm::IStr` mirrors this to share the read.
/// The byte-sized fields (`kind`/`color`/`alive`) precede the word-sized ones so
/// they pack into the leading word. The rest is the tricolor collector's state.
#[repr(C)]
pub(crate) struct GcInner<T: ?Sized> {
    kind: u8,
    color: Cell<u8>,
    #[cfg(feature = "gc_sanitize")]
    alive: AtomicBool,
    next: AtomicPtr<GcInner<()>>,
    finalize: fn(*mut GcInner<()>),
    size: usize,
    // `pub(crate)` so the JIT can address a cell's payload with dynasm's typed
    // offset (`offset_of!(GcInner<_>, val)`).
    pub(crate) val: T,
}

/// The cell-type tag for a heap payload `T`, written into `GcInner::kind` at
/// allocation. Non-cell allocations (upvalue slots, closed-upvalue boxes, etc.)
/// keep the default `0`, which is never read as an `LBoxed` pointer kind.
pub trait CellKind {
    fn cell_kind() -> u8 { 0 }
}
impl<T: ?Sized> CellKind for T {
    default fn cell_kind() -> u8 { 0 }
}

/// Read the offset-0 type tag of a raw cell pointer (a `GcInner` or a `vm::IStr`).
/// SAFETY: `addr` must point at a live cell whose layout starts with the tag.
#[inline(always)]
pub unsafe fn read_cell_kind(addr: u64) -> u8 {
    unsafe { *(addr as *const u8) }
}

/// Shades an object's immediate children. Carried in the worklist entry (not in `GcInner`)
/// since only worklisted objects are scanned and every push site knows the concrete type.
///
/// Unsafe because it blindly reinterprets `erased`: a caller must pass a pointer to a live
/// `GcInner<T>` for the `T` the thunk was instantiated with. Upheld by only ever pairing a
/// pointer with `scan_thunk::<T>` for its own `T`.
type ScanFn = unsafe fn(*const GcInner<()>, &Owner);

/// Monomorphized [`ScanFn`] for `GcInner<T>`: `val.mark` reaches each child `Gc`, whose
/// `mark` enqueues rather than recurses, so this visits exactly one level.
///
/// # Safety
/// See [`ScanFn`]: `erased` must point to a live `GcInner<T>`.
unsafe fn scan_thunk<T: Mark>(erased: *const GcInner<()>, owner: &Owner) {
    // SAFETY: `erased` is a `GcInner<T>` by the ScanFn contract.
    unsafe { (*(erased as *const GcInner<T>)).val.mark(owner) }
}

/// Type-erased pointer to a published root plus its shade thunk. See Note [GC roots].
#[derive(Clone, Copy)]
struct RootRef {
    ptr: *const (),
    mark: unsafe fn(*const (), &Owner),
}

/// Monomorphized [`Mark`] implementation for a type erased pointer, used for the rooted
/// list of objects.
///
/// # Safety:
/// `ptr` must point to a live `*const T`.
unsafe fn root_thunk<T: Mark>(ptr: *const (), owner: &Owner) {
    unsafe { (&*(ptr as *const T)).mark(owner) }
}

thread_local! {
    /// Per-thread GC heap; `const`-initialized so `hp()` is a bare TLS load on the allocation
    /// hot path. See Note [Scoped heap].
    static HEAP: UnsafeCell<Heap> = const { UnsafeCell::new(Heap::new()) };
}

/// Raw pointer to this thread's heap. All GC-internal mutation goes through raw field
/// projections off this pointer (never a `&mut Heap`), so that shading — which pushes
/// onto `heap.gray` — can run while other fields are being read without aliasing UB. The
/// address is stable for the life of the thread, so it may be held across calls.
#[inline]
fn hp() -> *mut Heap {
    HEAP.with(|h| h.get())
}

#[inline]
fn push_gray<T: Mark>(ptr: *const GcInner<T>) {
    unsafe { (*hp()).gray.push((ptr as *const GcInner<()>, scan_thunk::<T>)); }
}

/// Enqueue onto `grayagain`. See Note [Write barriers].
#[inline]
fn push_grayagain<T: Mark>(ptr: *const GcInner<T>) {
    unsafe { (*hp()).grayagain.push((ptr as *const GcInner<()>, scan_thunk::<T>)); }
}

pub struct Heap {
    top: AtomicPtr<GcInner<()>>,
    roots: BTreeMap<*const (), (Box<dyn Mark>, usize)>,
    /// Gray objects awaiting scanning, each with its scan thunk.
    gray: Vec<(*const GcInner<()>, ScanFn)>,
    /// Tables reverted by the backward barrier, drained in `finish`. See Note [Write barriers].
    grayagain: Vec<(*const GcInner<()>, ScanFn)>,
    phase: Phase,
    /// Live bytes tracked by the collector.
    total_bytes: usize,
    /// Cycle-trigger threshold for `total_bytes`.
    threshold: usize,
    /// Set by `collectgarbage("stop")` to disable automatic stepping.
    gc_off: bool,
    /// Which of {0,1} currently means white; flipped each cycle in `sweep_free`. Per-heap, so
    /// one thread's color flip can't reinterpret another thread's objects. See `white`/`black`.
    current_white: u8,
    state_root: Option<RootRef>,
    spec_root: Option<RootRef>,
}

impl Heap {
    const fn new() -> Self {
        Self {
            top: AtomicPtr::new(core::ptr::null_mut()),
            roots: BTreeMap::new(),
            gray: Vec::new(),
            grayagain: Vec::new(),
            phase: Phase::Idle,
            total_bytes: 0,
            threshold: INITIAL_THRESHOLD,
            gc_off: false,
            current_white: 0,
            state_root: None,
            spec_root: None,
        }
    }

    /// The per-thread heap is `const`-initialized on first access, so this only exists for
    /// call sites that want to be explicit (`Vm::new`, the gc tests).
    pub fn init() {}

    /// Free the whole heap, leaving the thread a fresh empty one for its next VM epoch. See
    /// Note [Scoped heap] for why this is called (and why it is sound) at scope exit.
    ///
    /// Reassigning runs `Heap::drop`, which frees every object on `top` without scanning them,
    /// then drops the worklists and root map. Nothing here reads the `'src`/`'intern` data the
    /// objects borrow, so it is sound even once those arenas are gone.
    ///
    /// # Safety
    ///   * No `Gc`/`Tc`/`LValue` from the outgoing epoch may be read afterwards: its backing is
    ///     freed here. `Vm::scope` upholds this by branding those values so they cannot escape.
    pub fn reset() {
        // SAFETY: the heap is per-thread (Note [Scoped heap]) with no other live borrow at a
        // scope boundary, so writing through `hp()` is exclusive.
        unsafe { *hp() = Heap::new(); }
    }

    /// Publish the current VM roots for the collector to shade. See Note [GC roots].
    #[inline]
    pub fn set_roots<S: Mark, P: Mark>(state: &S, spec: &P) {
        let heap = hp();
        unsafe {
            // SAFETY: We uphold the root_thunk invariant by only storing it with the
            // object of the same type it is parameterized over.
            (*heap).state_root = Some(RootRef { ptr: state as *const S as *const (), mark: root_thunk::<S> });
            (*heap).spec_root = Some(RootRef { ptr: spec as *const P as *const (), mark: root_thunk::<P> });
        }
    }

    /// Shade every root gray. Snapshots the root references first so no borrow of the
    /// heap is held while the shading pushes onto the gray worklist.
    ///
    /// # Safety:
    ///   * Must only be called with up-to-date [`Heap::set_roots`].
    unsafe fn mark_roots(owner: &Owner) {
        let heap = hp();
        let sr = unsafe { (*heap).state_root };
        let pr = unsafe { (*heap).spec_root };
        // SAFETY: Calling `mark` upholds `root_thunk`'s invariant by induction:
        // in order for it to be rooted initially it must have been alive, and by marking
        // all roots before collection we keep it alive moving forward.
        if let Some(r) = sr { (r.mark)(r.ptr, owner); }
        if let Some(r) = pr { (r.mark)(r.ptr, owner); }
        let root_ptrs: Vec<*const (dyn Mark)> = unsafe {
            (*heap).roots.values().map(|(b, _)| &**b as *const (dyn Mark)).collect()
        };
        for p in root_ptrs {
            unsafe { (&*p).mark(owner); }
        }
    }

    /// Pop and scan gray objects until either `budget` are processed or the worklist is
    /// empty. Returns true if the gray set is now empty.
    fn mark_some(owner: &Owner, budget: usize) -> bool {
        let mut n = 0;
        while n < budget {
            let entry = unsafe { (*hp()).gray.pop() };
            let Some((ptr, scan)) = entry else { return true; };
            unsafe {
                (*ptr).color.set(black());
                // SAFETY: `scan` was paired with `ptr` at its push site, so their `T` match.
                scan(ptr, owner);
            }
            n += 1;
        }
        unsafe { (*hp()).gray.is_empty() }
    }

    /// Free every white object, then flip the white/black interpretation so all survivors
    /// (currently black) become white for the next cycle without being rewritten. Must be
    /// called with the gray set fully drained (only white/black remain).
    ///
    /// # Safety:
    ///   * All GC objects which will be used after must have been marked.
    unsafe fn sweep_free(_owner: &Owner) {
        let heap = hp();
        let dead = white();
        let mut prev: *mut AtomicPtr<GcInner<()>> = unsafe { &raw mut (*heap).top };
        let mut current = unsafe { (*heap).top.load(Ordering::Acquire) };
        while current != core::ptr::null_mut() {
            let next_ptr = unsafe { (*current).next.load(Ordering::Acquire) };
            if unsafe { (*current).color.get() } == dead {
                debug!("freeing {current:p}");
                unsafe {
                    (*prev).store(next_ptr, Ordering::Release);
                    (*heap).total_bytes = (*heap).total_bytes.saturating_sub((*current).size);
                    ((*current).finalize)(current.cast());
                }
            } else {
                prev = unsafe { &raw mut (*current).next };
            }
            current = next_ptr;
        }
        // Survivors are black; flipping makes them the new white. New black == old dead,
        // which no live object holds.
        unsafe { (*heap).current_white = dead ^ 1; }
    }

    /// Atomic tail of a cycle: fold in grayagain, re-scan the roots, drain, sweep, and
    /// re-arm the threshold. See Note [Incremental GC], Note [Write barriers].
    ///
    /// # Safety:
    ///   * Must only be called with up-to-date [`Heap::set_roots`].
    ///   * All GC objects which will be used after must have been marked.
    unsafe fn finish(owner: &Owner) {
        unsafe {
            // The mutator is stopped, so grayagain is final; the roots need re-scanning
            // because the value stack has no barrier.
            let hp = hp();
            let mut ga = core::mem::take(&mut (*hp).grayagain);
            (*hp).gray.append(&mut ga);
            Self::mark_roots(owner);
            Self::mark_some(owner, usize::MAX);
            Self::sweep_free(owner);
        }
        let heap = hp();
        unsafe {
            (*heap).phase = Phase::Idle;
            let live = (*heap).total_bytes;
            (*heap).threshold = core::cmp::max(MIN_THRESHOLD, live.saturating_mul(2));
        }
    }

    /// One incremental step: start a cycle if over threshold, otherwise scan a bounded
    /// budget, finishing when the worklist empties. Idle+under-threshold is a load and
    /// compare. See Note [Incremental GC]. Private worker behind the `GcCtx` token.
    ///
    /// # Safety: See [`Heap::finish`].
    unsafe fn step_inner(owner: &Owner) {
        let heap = hp();
        unsafe {
            if (*heap).gc_off { return; }

            // gc_stress: collect on every allocation, one object per step, to exercise the
            // barriers and worklist maximally.
            #[cfg(feature = "gc_stress")]
            let (trigger, budget) = (0usize, 1usize);
            #[cfg(not(feature = "gc_stress"))]
            let (trigger, budget) = ((*heap).threshold, STEP_BUDGET);

            match (*heap).phase {
                Phase::Idle => {
                    if (*heap).total_bytes < trigger { return; }
                    (*heap).phase = Phase::Mark;
                    Self::mark_roots(owner);
                }
                Phase::Mark => {}
            }

            if Self::mark_some(owner, budget) {
                Self::finish(owner);
            }
        }
    }

    /// Full synchronous collection reclaiming everything unreachable at the call (as Lua's
    /// `luaC_fullgc`). Two cycles are required: the first finishes the in-progress cycle
    /// but retains objects that died mid-cycle (already shaded — floating garbage); the
    /// second, with them white again, reclaims them. Private worker behind the `GcCtx` token.
    ///
    /// # Safety: See [`Heap::finish`].
    unsafe fn full_collect_inner(owner: &Owner) {
        let heap = hp();
        unsafe {
            (*heap).phase = Phase::Mark;
            Self::finish(owner);
            (*heap).phase = Phase::Mark;
            Self::finish(owner);
        }
    }

    /// Live bytes currently tracked. Backs `collectgarbage("count")`.
    pub fn live_bytes() -> usize {
        unsafe { (*hp()).total_bytes }
    }

    /// Enable/disable automatic collection. Backs `collectgarbage("stop"/"restart")`.
    pub fn set_gc_off(off: bool) {
        unsafe { (*hp()).gc_off = off; }
    }

    /// Run a collection to completion from the roots plus anything already shaded (the gc
    /// unit tests shade manually via `Mark::mark`). Private worker behind the `GcCtx` token.
    ///
    /// SAFETY: See [`Heap::finish`].
    unsafe fn sweep_inner(owner: &Owner) {
        unsafe {
            (*hp()).phase = Phase::Mark;
            Self::finish(owner);
        }
    }

    /// Run `f` in a rooting scope, handing it the `GcCtx` token that gates collection.
    /// Roots clear when `f` returns or panics; the higher-ranked `'lua` brand stops the
    /// token escaping. See Note [GC roots].
    pub fn rooted<R>(f: impl for<'lua> FnOnce(GcCtx<'lua>) -> R) -> R {
        let scope = RootScope { _priv: () };
        f(scope.token())
    }

    /// RAII form of [`Heap::rooted`] for call sites that can't wrap their body in a closure
    /// (the interpreter loop): hold the guard for the run and take tokens from
    /// [`RootScope::token`]. See Note [GC roots].
    pub fn root_scope() -> RootScope {
        RootScope { _priv: () }
    }

    /// Root a GC pointer, so that it is automatically marked by the GC before any sweep.
    ///
    /// # SAFETY: The caller is required to guarantee that GC object is unrooted before freeing
    /// it, and that the root doesn't outlive any lifetimes attached to the object.
    // TODO: Replace with Root smartpointer instead.
    pub unsafe fn root<T: Mark>(gc: &mut Gc<T>, _owner: &mut Owner) {
        // SAFETY: We have owner. Maybe still kinda sus think about this some more
        let heap = hp();
        // Increment the root count for this key
        let ptr = gc.ptr.as_ptr();
        let dt: Box<Gc<T>> = Box::new(gc.clone());
        // SAFETY: Erase the lifetime of Gc<T>. The caller is required to not have the
        // object remain rooted longer than its lifetimes.
        let dt: Box<dyn Mark> = unsafe { core::mem::transmute(dt as Box<dyn Mark>) };
        unsafe { (*heap).roots.entry(ptr.cast()).or_insert_with(|| (dt, 0)).1 += 1; }
    }

    unsafe fn unroot<T>(gc: &Gc<T>, _owner: &mut Owner) {
        // No-op for now? The stack rooting API is unsafe to use until this is implemented,
        // but the [`Heap::root`] invariant requires callers who would want to use it
        // to hit this as a blocker.
        unimplemented!()
    }
}

/// RAII scope that clears the published roots on drop and mints `GcCtx` tokens (borrowed
/// from it, so they can't outlive it) via [`RootScope::token`]. See Note [GC roots].
#[must_use = "dropping the RootScope immediately clears the GC roots"]
pub struct RootScope {
    _priv: (),
}

impl RootScope {
    /// Mint a capability token, borrowed from this scope so it can't escape.
    #[inline]
    pub fn token<'lua>(&'lua self) -> GcCtx<'lua> {
        GcCtx { _brand: PhantomData }
    }
}

impl Drop for RootScope {
    fn drop(&mut self) {
        let heap = hp();
        unsafe {
            (*heap).state_root = None;
            (*heap).spec_root = None;
        }
    }
}

/// Capability token proving a rooting scope is active; every collection entry point takes
/// one. `Copy`, so it threads freely; the invariant `'lua` brand keeps it from escaping
/// the scope. See Note [GC roots].
#[derive(Clone, Copy)]
pub struct GcCtx<'lua> {
    _brand: PhantomData<fn(&'lua ()) -> &'lua ()>,
}

impl<'lua> GcCtx<'lua> {
    /// Publish the live roots and advance the incremental collector one bounded step.
    ///
    /// This is a garbage collection safepoint. See Note [GC roots].
    ///
    /// # Safety:
    ///   * All GC objects must either be rooted or added to the object graph.
    #[inline]
    pub unsafe fn step<S: Mark, P: Mark>(self, state: &S, spec: &P, owner: &Owner) {
        Heap::set_roots(state, spec);
        // SAFETY:
        //  * We just updated set_roots.
        //  * Live GC variables are all reachable by our own invariant.
        unsafe { Heap::step_inner(owner) };
    }

    /// Publish the live roots and run a full synchronous collection.
    ///
    /// This is a garbage collection safepoint. See Note [GC roots].
    ///
    /// # Safety:
    ///   * All GC objects must either be rooted or added to the object graph.
    pub unsafe fn full_collect<S: Mark, P: Mark>(self, state: &S, spec: &P, owner: &Owner) {
        Heap::set_roots(state, spec);
        // SAFETY:
        //  * We just updated set_roots.
        //  * Live GC variables are all reachable by our own invariant.
        unsafe { Heap::full_collect_inner(owner) };
    }

    /// Sweep using the roots published so far (plus the permanent `Heap::root` set).
    /// Used by the gc unit tests, which shade objects manually with `Mark::mark`.
    ///
    /// # Safety: See [`Heap::finish`].
    pub unsafe fn sweep(self, owner: &Owner) {
        unsafe { Heap::sweep_inner(owner) };
    }

    /// Publish the live roots without collecting, so a native function entered next (e.g.
    /// `collectgarbage`) can reach them.
    #[inline]
    pub fn publish<S: Mark, P: Mark>(self, state: &S, spec: &P) {
        Heap::set_roots(state, spec);
    }

    /// Full collection using the most recently published roots. For `collectgarbage`,
    /// which cannot receive a token through the fixed native ABI.
    ///
    /// # Safety: See [`Heap::finish`]. Must be called with an up-to-date [`Heap::set_roots`].
    pub unsafe fn full_collect_published(self, owner: &Owner) {
        unsafe { Heap::full_collect_inner(owner) };
    }

    /// One incremental step using the most recently published roots (for `collectgarbage`).
    ///
    /// # Safety: See [`Heap::finish`]. Must be called with an up-to-date [`Heap::set_roots`].
    pub unsafe fn step_published(self, owner: &Owner) {
        unsafe { Heap::step_inner(owner) };
    }

    /// SAFETY: only sound inside a live rooting scope whose roots are currently published —
    /// which the VM guarantees for natives (a safepoint calls `publish` just before the
    /// call). See Note [GC roots].
    #[inline]
    pub unsafe fn assume_rooted() -> GcCtx<'lua> {
        GcCtx { _brand: PhantomData }
    }
}

impl Drop for Heap {
    fn drop(&mut self) {
        let mut current = self.top.load(Ordering::Acquire);
        while current != core::ptr::null_mut() {
            unsafe {
                let next = (*current).next.load(Ordering::Acquire);
                ((*current).finalize)(current.cast());
                current = next;
            }
        }
    }
}

#[cfg(all(test, feature = "gc_test"))]
mod test {
    use super::*;
    #[test]
    fn gc_works() {
        Heap::init();
        let a = Gc::new(1);
        assert_eq!(*a, 1);
    }

    #[test]
    fn gc_can_mark() {
        Heap::init();
        let a = Gc::new(1);
        let owner = Owner::new();
        a.mark(&owner);
        assert_eq!(*a, 1);
    }

    #[test]
    fn gc_sweep_empty() {
        Heap::init();
        let owner = Owner::new();
        Heap::rooted(|gc| unsafe { gc.sweep(&owner) });
    }

    #[cfg(feature = "gc_sanitize")]
    #[test]
    fn gc_sweep_keeps_marks_alive() {
        Heap::init();
        let a = Gc::new(1);
        let owner = Owner::new();
        a.mark(&owner);
        Heap::rooted(|gc| unsafe { gc.sweep(&owner) });
        assert_eq!(*a, 1);
    }

    #[cfg(feature = "gc_sanitize")]
    #[test]
    fn gc_sweep_keeps_marks_alive_twice() {
        Heap::init();
        let a = Gc::new(1);
        let owner = Owner::new();
        a.mark(&owner);
        Heap::rooted(|gc| unsafe { gc.sweep(&owner) });
        a.mark(&owner);
        Heap::rooted(|gc| unsafe { gc.sweep(&owner) });
        assert_eq!(*a, 1);
    }

    #[cfg(feature = "gc_sanitize")]
    #[test]
    fn gc_sweep_keeps_roots_alive() {
        Heap::init();
        let mut a = Gc::new(1);
        let mut owner = Owner::new();
        unsafe { Heap::root(&mut a, &mut owner) };
        Heap::rooted(|gc| unsafe { gc.sweep(&owner) });
        assert_eq!(*a, 1);
    }

    #[cfg(feature = "gc_sanitize")]
    #[test]
    fn gc_sweep_keeps_roots_alive_twice() {
        Heap::init();
        let mut a = Gc::new(1);
        let mut owner = Owner::new();
        unsafe { Heap::root(&mut a, &mut owner) };
        Heap::rooted(|gc| unsafe { gc.sweep(&owner) });
        Heap::rooted(|gc| unsafe { gc.sweep(&owner) });
        assert_eq!(*a, 1);
    }

    #[cfg(feature = "gc_sanitize")]
    #[test]
    #[should_panic]
    fn gc_sweep_frees_unmarked() {
        Heap::init();
        let a = Gc::new(1);
        let mut owner = Owner::new();
        Heap::rooted(|gc| unsafe { gc.sweep(&owner) });
        assert_eq!(*a, 1); // should panic
    }

    #[cfg(feature = "gc_sanitize")]
    #[test]
    #[should_panic]
    fn gc_sweep_traverses_one() {
        Heap::init();
        let a = Gc::new(1);
        let b = Gc::new(2);
        let mut owner = Owner::new();
        a.mark(&owner);
        Heap::rooted(|gc| unsafe { gc.sweep(&owner) });
        assert_eq!(*a, 1);
        assert_eq!(*b, 2); // should panic
    }

    #[cfg(feature = "gc_sanitize")]
    #[test]
    fn gc_sweep_unlinks() {
        Heap::init();
        let a = Gc::new(1);
        let b = Gc::new(2);
        let mut owner = Owner::new();
        b.mark(&owner);
        Heap::rooted(|gc| unsafe { gc.sweep(&owner) });
        b.mark(&owner);
        Heap::rooted(|gc| unsafe { gc.sweep(&owner) });
        assert_eq!(*b, 2);
    }

    #[cfg(feature = "gc_sanitize")]
    #[test]
    fn gc_sweep_unlinks_two() {
        Heap::init();
        let a = Gc::new(1);
        let b = Gc::new(2);
        let c = Gc::new(3);
        let mut owner = Owner::new();
        a.mark(&owner);
        c.mark(&owner);
        Heap::rooted(|gc| unsafe { gc.sweep(&owner) });
        c.mark(&owner);
        Heap::rooted(|gc| unsafe { gc.sweep(&owner) });
        c.mark(&owner);
        Heap::rooted(|gc| unsafe { gc.sweep(&owner) });
        assert_eq!(*c, 3);
    }
}
