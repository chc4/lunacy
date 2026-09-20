use std::ops::{Deref, DerefMut};
use std::hash::Hash;
use std::rc::Rc;
use std::cell::Cell;
use std::marker::PhantomData;
use std::collections::BTreeMap;
use std::sync::atomic::{Ordering, AtomicBool, AtomicPtr};
use crate::vm::{Tc, TcOwner, LValue, LClosure, NClosure, Table, Upvalue};
use crate::{TCell, TCellOwner};
use indexmap::IndexMap;
use crate::debug;

pub trait Mark {
    fn mark(&self, owner: &TCellOwner<TcOwner>);
}

impl<'src, 'intern> Mark for LValue<'src, 'intern> {
    fn mark(&self, owner: &TCellOwner<TcOwner>) {
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

// All types are Mark by default
impl<T> Mark for T {
    default fn mark(&self, owner: &TCellOwner<TcOwner>) {
        if const { std::intrinsics::needs_drop::<T>() } {
            panic!("default Mark for non-trivial drop {}", const { std::intrinsics::type_name::<T>() })
        }
    }
}

impl<T> Mark for Tc<T> {
    fn mark(&self, owner: &TCellOwner<TcOwner>) {
        self.0.mark(owner)
    }
}

impl<T: Mark> Mark for TCell<TcOwner, T> {
    fn mark(&self, owner: &TCellOwner<TcOwner>) {
        self.ro(owner).mark(owner)
    }
}

impl<T> Mark for Rc<T> {
    fn mark(&self, owner: &TCellOwner<TcOwner>) {
        self.deref().mark(owner)
    }
}

impl<T> Mark for Box<T> {
    fn mark(&self, owner: &TCellOwner<TcOwner>) {
        self.deref().mark(owner)
    }
}

impl Mark for Box<dyn Mark> {
    fn mark(&self, owner: &TCellOwner<TcOwner>) {
        self.deref().mark(owner)
    }
}

impl<'src, 'intern> Mark for Table<'src, 'intern> {
    fn mark(&self, owner: &TCellOwner<TcOwner>) {
        for item in self.array.iter() {
            item.mark(owner);
        }
        self.hash.mark(owner);
    }
}

impl<'src, 'intern> Mark for LClosure<'src, 'intern> {
    fn mark(&self, owner: &TCellOwner<TcOwner>) {
        for upval in self.upvalues.iter() {
            upval.mark(owner);
        }
    }
}

impl Mark for NClosure {
    fn mark(&self, _owner: &TCellOwner<TcOwner>) { }
}

impl<'src, 'intern> Mark for Upvalue<'src, 'intern> {
    fn mark(&self, owner: &TCellOwner<TcOwner>) {
        if let Upvalue::Closed(o) = self {
            o.mark(owner)
        }
    }
}

impl<K: Mark, V: Mark, S> Mark for IndexMap<K, V, S> {
    fn mark(&self, owner: &TCellOwner<TcOwner>) {
        for (k, v) in self {
            k.mark(owner);
            v.mark(owner);
        }
    }
}

impl<T: Mark> Mark for Vec<T> {
    fn mark(&self, owner: &TCellOwner<TcOwner>) {
        for item in self.iter() {
            item.mark(owner);
        }
    }
}

// ===== Tricolor incremental garbage collector =====
//
// Objects are one of three colors, stored in `GcInner::color`:
//   WHITE - not yet reached this cycle (candidate for collection)
//   GRAY  - reached, but its children have not been scanned yet (on the gray worklist)
//   BLACK - reached and fully scanned; the strong tricolor invariant says a black
//           object may never point directly at a white one.
//
// Marking is *incremental*: at each GC safepoint we shade the roots and then scan a
// bounded budget of gray objects, spreading the mark phase across many safepoints
// instead of pausing for a full traversal.
//
// To keep the tricolor invariant while the mutator runs between increments we use two
// write barriers, split the same way Lua does:
//
//   * Non-table objects use a *forward* (Dijkstra) barrier (`Gc::write_barrier`): storing
//     a pointer to `value` into a black container shades `value` gray, advancing the
//     frontier to it. The container stays black. Work is pushed *forward* onto the
//     incremental gray worklist and traced by ordinary mark steps; nothing is deferred to
//     the atomic phase and nothing is re-scanned, so a mutation loop can't starve.
//
//   * Tables use a *backward* barrier (`Gc::backward_barrier`, Lua's `barrierback`):
//     mutating a black table reverts it to gray and links it onto the `grayagain` list,
//     without shading the written value. Tables are the most frequently mutated objects,
//     so shading every written value (forward) would be costly; instead we re-scan the
//     whole table once, in the atomic finish. The `color == BLACK` guard means each table
//     joins `grayagain` at most once per cycle, and it is *not* put on the incremental
//     `gray` worklist (that could let a hot loop re-gray it forever), so no starvation.
//     The cost is that `finish` traces the white sub-graph reachable from mutated tables
//     in the stop-the-world phase — Lua accepts this trade for tables.
//
// Both barriers fire at the store sites (where the container — and, for the forward one,
// the value — are visible). They are self-gating: the `is_black` check is false while idle
// (nothing is black between cycles), so the fast path is a single load + branch.
//
// When the incremental gray set empties we perform an atomic finish that folds in
// `grayagain` (the backward-barrier'd tables), re-scans the roots (the value stack /
// registers have no barrier, so the mutator may have dropped a white object into a
// register since the last scan) and drains whatever those shade, then an atomic sweep.
// Because sweep is atomic (no allocation interleaves with it) a single white color is
// sufficient — new objects are always allocated white and only ever swept after a
// completed atomic mark.
const WHITE: u8 = 0;
const GRAY: u8 = 1;
const BLACK: u8 = 2;

/// Gray objects scanned per incremental step during normal operation.
const STEP_BUDGET: usize = 512;
/// Never let the trigger threshold drop below this, to avoid thrashing when the live
/// set is tiny.
const MIN_THRESHOLD: usize = 256 * 1024;
/// Bytes of live heap before the first collection cycle starts.
const INITIAL_THRESHOLD: usize = 1024 * 1024;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Phase {
    /// No collection in progress.
    Idle,
    /// Incrementally marking reachable objects.
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

    pub fn new(val: T) -> Self {
        let heap = hp();
        let size = core::mem::size_of::<GcInner<T>>();
        let mut top = unsafe { (*heap).top.load(Ordering::Acquire) };
        let inner = GcInner {
            next: AtomicPtr::new(top),
            // New objects are born white: if nothing reaches them this cycle they are
            // reclaimed on the next sweep.
            color: Cell::new(WHITE),
            size,
            // Scan-one-level thunk: shades this object's immediate children gray. The
            // recursion in the `Mark` impls stops at each `Gc` boundary (which merely
            // enqueues), so calling `val.mark` here visits exactly one level.
            scan: |erased, owner| unsafe {
                let typed = erased as *const GcInner<T>;
                (*typed).val.mark(owner);
            },
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
        // Account for the allocation. The safepoints consult `total_bytes` to decide
        // when to start a cycle; `Gc::new` has no owner/roots so it can't step itself.
        unsafe { (*heap).total_bytes += size; }
        Self { ptr: core::ptr::NonNull::new(ptr as _).unwrap() }
    }

    /// True if this object has been fully scanned this cycle (black).
    #[inline]
    pub fn is_black(&self) -> bool {
        unsafe { (*self.ptr.as_ptr()).color.get() == BLACK }
    }

    /// Forward (Dijkstra) write barrier. Call at every store of a pointer `value` into
    /// this object. If `self` is black, storing a pointer to a (possibly white) `value`
    /// would break the "no black -> white" invariant, so shade `value` — pushing the
    /// marking frontier forward onto the incremental gray worklist. `self` stays black, so
    /// there is no re-scanning and no way for a mutation loop to starve the collector; the
    /// shaded value is traced by ordinary mark steps. No-op while idle (nothing is black),
    /// so the fast path is a single load + branch.
    #[inline]
    pub fn write_barrier<V: Mark>(&self, value: &V, owner: &TCellOwner<TcOwner>) {
        if self.is_black() {
            value.mark(owner);
        }
    }

    /// Backward write barrier (Lua's `barrierback`), used only for tables. Mutating a black
    /// table reverts it to gray and links it onto `grayagain` to be re-scanned once in the
    /// atomic `finish` — cheaper per-write than the forward barrier (no value shading) for
    /// the frequently-mutated tables. It is NOT put on the incremental `gray` worklist, and
    /// the `color == BLACK` guard means it joins `grayagain` at most once per cycle, so a
    /// hot mutation loop can't starve the collector. No-op while idle.
    #[inline]
    pub fn backward_barrier(&self) {
        let inner = self.ptr.as_ptr();
        unsafe {
            if (*inner).color.get() == BLACK {
                (*inner).color.set(GRAY);
                push_grayagain(inner as *const GcInner<()>);
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

impl<T> DerefMut for Gc<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        #[cfg(feature = "gc_sanitize")]
        unsafe { assert!(self.ptr.as_ref().alive.load(Ordering::Acquire), "value is dead") };
        unsafe { &mut self.ptr.as_mut().val }
    }
}

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
    /// Shading: white -> gray (and enqueue). Unlike the old collector this does *not*
    /// recurse; the gray worklist drives scanning one level at a time.
    fn mark(&self, _owner: &TCellOwner<TcOwner>) {
        let inner = self.ptr.as_ptr();
        unsafe {
            if (*inner).color.get() == WHITE {
                (*inner).color.set(GRAY);
                push_gray(inner as *const GcInner<()>);
            }
        }
    }
}

#[repr(C)]
struct GcInner<T: ?Sized> {
    next: AtomicPtr<GcInner<()>>,
    finalize: fn(*mut GcInner<()>),
    scan: fn(*const GcInner<()>, &TCellOwner<TcOwner>),
    color: Cell<u8>,
    size: usize,
    #[cfg(feature = "gc_sanitize")]
    alive: AtomicBool,
    val: T,
}

/// A type-erased reference to a live root (the interpreter's `RunState` and the JIT
/// `Specializer`). Refreshed at every safepoint / before every native call so that the
/// collector — and `collectgarbage`, which only receives an owner — can find the roots.
#[derive(Clone, Copy)]
struct RootRef {
    ptr: *const (),
    mark: fn(*const (), &TCellOwner<TcOwner>),
}

fn root_thunk<T: Mark>(ptr: *const (), owner: &TCellOwner<TcOwner>) {
    unsafe { (&*(ptr as *const T)).mark(owner) }
}

static HEAP: AtomicPtr<Heap> = AtomicPtr::new(core::ptr::null_mut());

/// Raw pointer to the global heap. All GC-internal mutation goes through raw field
/// projections off this pointer (never a `&mut Heap`), so that shading — which pushes
/// onto `heap.gray` — can run while other fields are being read without aliasing UB.
#[inline]
fn hp() -> *mut Heap {
    HEAP.load(Ordering::Acquire)
}

#[inline]
fn push_gray(ptr: *const GcInner<()>) {
    unsafe { (*hp()).gray.push(ptr); }
}

/// Tables reverted to gray by the backward barrier: re-scanned once, atomically, in
/// `finish` (never fed into the incremental `gray` worklist).
#[inline]
fn push_grayagain(ptr: *const GcInner<()>) {
    unsafe { (*hp()).grayagain.push(ptr); }
}

pub struct Heap {
    top: AtomicPtr<GcInner<()>>,
    roots: BTreeMap<*const (), (Box<dyn Mark>, usize)>,
    /// Worklist of gray objects awaiting scanning.
    gray: Vec<*const GcInner<()>>,
    /// Tables turned back to gray by the backward barrier; folded into `gray` and drained
    /// once during the atomic `finish` (Lua's `grayagain`).
    grayagain: Vec<*const GcInner<()>>,
    phase: Phase,
    /// Live bytes currently tracked by the collector.
    total_bytes: usize,
    /// Start a cycle once `total_bytes` reaches this.
    threshold: usize,
    /// `collectgarbage("stop")` disables automatic stepping.
    gc_off: bool,
    state_root: Option<RootRef>,
    spec_root: Option<RootRef>,
}

impl Default for Heap {
    fn default() -> Self {
        Self {
            top: AtomicPtr::new(core::ptr::null_mut()),
            roots: BTreeMap::new(),
            gray: Vec::new(),
            grayagain: Vec::new(),
            phase: Phase::Idle,
            total_bytes: 0,
            threshold: INITIAL_THRESHOLD,
            gc_off: false,
            state_root: None,
            spec_root: None,
        }
    }
}

impl Heap {
    pub fn init() {
        if HEAP.load(Ordering::Acquire) == core::ptr::null_mut() {
            let heap: &mut Heap = Box::leak(Box::new(Heap::default()));
            if let Err(_) = HEAP.compare_exchange(core::ptr::null_mut(), heap,
                Ordering::Release, Ordering::Acquire)
            {
                // Someone else initialized the heap instead. Deallocate ours because it won't be
                // used.
                // SAFETY: The cmpxchg failed, which means its unreachable.
                unsafe { drop(Box::from_raw(heap)) };
            }
        }
    }

    /// Register the current VM roots so incremental stepping and `collectgarbage` can
    /// reach them. The pointers are only ever dereferenced synchronously (during a step
    /// or a native call in the same interpreter iteration), while the referents live at
    /// a stable address.
    #[inline]
    pub fn set_roots<S: Mark, P: Mark>(state: &S, spec: &P) {
        let heap = hp();
        unsafe {
            (*heap).state_root = Some(RootRef { ptr: state as *const S as *const (), mark: root_thunk::<S> });
            (*heap).spec_root = Some(RootRef { ptr: spec as *const P as *const (), mark: root_thunk::<P> });
        }
    }

    /// Shade every root gray. Snapshots the root references first so no borrow of the
    /// heap is held while the shading pushes onto the gray worklist.
    unsafe fn mark_roots(owner: &TCellOwner<TcOwner>) {
        let heap = hp();
        let sr = unsafe { (*heap).state_root };
        let pr = unsafe { (*heap).spec_root };
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
    unsafe fn mark_some(owner: &TCellOwner<TcOwner>, budget: usize) -> bool {
        let mut n = 0;
        while n < budget {
            let ptr = unsafe { (*hp()).gray.pop() };
            let Some(ptr) = ptr else { return true; };
            unsafe {
                (*ptr).color.set(BLACK);
                ((*ptr).scan)(ptr, owner);
            }
            n += 1;
        }
        unsafe { (*hp()).gray.is_empty() }
    }

    /// Free every white object and recolor survivors back to white for the next cycle.
    /// Must be called with the gray set fully drained (only white/black remain).
    unsafe fn sweep_free(_owner: &TCellOwner<TcOwner>) {
        let heap = hp();
        let mut prev: *mut AtomicPtr<GcInner<()>> = unsafe { &raw mut (*heap).top };
        let mut current = unsafe { (*heap).top.load(Ordering::Acquire) };
        while current != core::ptr::null_mut() {
            let next_ptr = unsafe { (*current).next.load(Ordering::Acquire) };
            if unsafe { (*current).color.get() } == WHITE {
                debug!("freeing {current:p}");
                unsafe {
                    (*prev).store(next_ptr, Ordering::Release);
                    (*heap).total_bytes = (*heap).total_bytes.saturating_sub((*current).size);
                    ((*current).finalize)(current.cast());
                }
            } else {
                // Survived: reset to white for the next cycle.
                unsafe { (*current).color.set(WHITE); }
                prev = unsafe { &raw mut (*current).next };
            }
            current = next_ptr;
        }
    }

    /// Finish the collection atomically: rescan the roots (catching anything the mutator
    /// stashed only on the stack since the cycle began), drain the remaining gray set,
    /// sweep, and re-arm the trigger threshold.
    unsafe fn finish(owner: &TCellOwner<TcOwner>) {
        unsafe {
            // Fold the backward-barrier'd tables into the gray worklist for a single atomic
            // rescan (each appears at most once per cycle; the mutator is stopped now, so
            // the barrier can't add more).
            let hp = hp();
            let mut ga = core::mem::take(&mut (*hp).grayagain);
            (*hp).gray.append(&mut ga);
            // Re-scan the roots with the mutator stopped: the value stack / registers have
            // no write barrier, so the mutator may have dropped a white object into a
            // register since the last scan. The forward barrier kept every non-table heap
            // edge sound already; this plus draining is all the atomic phase needs.
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

    /// Perform one incremental step of collection. Cheap (a load + compare) when idle
    /// and under the trigger threshold — this is the common case that makes the new
    /// collector fast, versus the old "full collect on every allocation".
    ///
    /// Private worker: callers must go through the `GcCtx` token (see `Heap::rooted`),
    /// which guarantees the roots are published first.
    unsafe fn step_inner(owner: &TCellOwner<TcOwner>) {
        let heap = hp();
        unsafe {
            if (*heap).gc_off { return; }

            // Under gc_stress, collect as aggressively and incrementally as possible
            // (start immediately, one object per step) to exercise the barrier + gray
            // worklist on every allocation.
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

    /// Synchronously run a full collection, reclaiming *all* currently-unreachable
    /// objects. Private worker behind the `GcCtx` token.
    ///
    /// Runs two cycles (like Lua's `luaC_fullgc`). The first finishes any in-progress
    /// incremental cycle; but objects that became unreachable *during* that cycle were
    /// already shaded and so are retained as floating garbage. The second cycle starts
    /// fresh (they are white again) and reclaims them, so a single
    /// `collectgarbage("collect")` frees everything dead at the call, matching Lua.
    unsafe fn full_collect_inner(owner: &TCellOwner<TcOwner>) {
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

    /// Sweep all allocation and free unmarked objects: shades all registered roots,
    /// drains the gray worklist (including anything shaded via `Gc::mark` beforehand),
    /// then frees the white objects. Private worker behind the `GcCtx` token.
    /// SAFETY: Any objects not reachable from the roots / prior shading must not be used
    /// afterwards.
    unsafe fn sweep_inner(owner: &TCellOwner<TcOwner>) {
        unsafe {
            (*hp()).phase = Phase::Mark;
            Self::finish(owner);
        }
    }

    /// Enter a rooting scope via a closure. The `GcCtx` token handed to `f` is the only
    /// way to drive a collection; when `f` returns (or panics) the published roots are
    /// cleared, so a stray later collection can never read a dangling root pointer. The
    /// higher-ranked `'lua` brand makes the token un-storable outside the scope.
    pub fn rooted<R>(f: impl for<'lua> FnOnce(GcCtx<'lua>) -> R) -> R {
        let scope = RootScope { _priv: () };
        f(scope.token())
    }

    /// Manual (RAII) form of [`Heap::rooted`], for call sites (like the interpreter loop)
    /// that can't wrap their whole body in a closure. Hold the returned guard for the
    /// duration of the run and obtain tokens from it via [`RootScope::token`]; roots are
    /// cleared when the guard drops.
    pub fn root_scope() -> RootScope {
        RootScope { _priv: () }
    }

    /// Root a GC pointer, so that it is automatically marked by the GC before any sweep.
    /// The caller is required to guarantee that GC object is unrooted before freeing
    /// it, and that the root doesn't outlive any lifetimes attached to the object.
    // TODO: Replace with Root smartpointer instead.
    pub unsafe fn root<T: Mark>(gc: &mut Gc<T>, owner: &mut TCellOwner<TcOwner>) {
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

    fn unroot<T>(gc: &Gc<T>, owner: &mut TCellOwner<TcOwner>) {
        // No-op for now?
    }
}

/// RAII scope that publishes VM roots and clears them on drop. Obtained from
/// [`Heap::root_scope`] (or created internally by [`Heap::rooted`]). Hand out `GcCtx`
/// tokens via [`RootScope::token`]; a token borrows the scope, so it cannot outlive it.
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
        // Clear the published roots so a later stray collection can't read a dangling
        // RunState/Specializer pointer.
        let heap = hp();
        unsafe {
            (*heap).state_root = None;
            (*heap).spec_root = None;
        }
    }
}

/// A `'lua`-branded capability token: proof that we are inside a rooting scope. Every
/// collection entry point requires one, so it is impossible to sweep without having
/// published roots. `Copy`, so it threads freely (e.g. into `Specializer::run`); the
/// invariant `'lua` brand keeps it from being stored beyond the scope.
#[derive(Clone, Copy)]
pub struct GcCtx<'lua> {
    _brand: PhantomData<fn(&'lua ()) -> &'lua ()>,
}

impl<'lua> GcCtx<'lua> {
    /// Publish the live roots and advance the incremental collector one bounded step.
    #[inline]
    pub fn step<S: Mark, P: Mark>(self, state: &S, spec: &P, owner: &TCellOwner<TcOwner>) {
        Heap::set_roots(state, spec);
        unsafe { Heap::step_inner(owner) };
    }

    /// Publish the live roots and run a full synchronous collection.
    pub fn full_collect<S: Mark, P: Mark>(self, state: &S, spec: &P, owner: &TCellOwner<TcOwner>) {
        Heap::set_roots(state, spec);
        unsafe { Heap::full_collect_inner(owner) };
    }

    /// Sweep using the roots published so far (plus the permanent `Heap::root` set).
    /// Used by the gc unit tests, which shade objects manually with `Mark::mark`.
    pub fn sweep(self, owner: &TCellOwner<TcOwner>) {
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
    pub fn full_collect_published(self, owner: &TCellOwner<TcOwner>) {
        unsafe { Heap::full_collect_inner(owner) };
    }

    /// One incremental step using the most recently published roots (for `collectgarbage`).
    pub fn step_published(self, owner: &TCellOwner<TcOwner>) {
        unsafe { Heap::step_inner(owner) };
    }

    /// SAFETY: only sound while executing inside a live rooting scope with roots currently
    /// published. The VM upholds this: a native function is only ever invoked from a
    /// safepoint that has just called [`GcCtx::publish`].
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
        let owner = TCellOwner::new();
        a.mark(&owner);
        assert_eq!(*a, 1);
    }

    #[test]
    fn gc_sweep_empty() {
        Heap::init();
        let owner = TCellOwner::new();
        Heap::rooted(|gc| gc.sweep(&owner));
    }

    #[cfg(feature = "gc_sanitize")]
    #[test]
    fn gc_sweep_keeps_marks_alive() {
        Heap::init();
        let a = Gc::new(1);
        let owner = TCellOwner::new();
        a.mark(&owner);
        Heap::rooted(|gc| gc.sweep(&owner));
        assert_eq!(*a, 1);
    }

    #[cfg(feature = "gc_sanitize")]
    #[test]
    fn gc_sweep_keeps_marks_alive_twice() {
        Heap::init();
        let a = Gc::new(1);
        let owner = TCellOwner::new();
        a.mark(&owner);
        Heap::rooted(|gc| gc.sweep(&owner));
        a.mark(&owner);
        Heap::rooted(|gc| gc.sweep(&owner));
        assert_eq!(*a, 1);
    }

    #[cfg(feature = "gc_sanitize")]
    #[test]
    fn gc_sweep_keeps_roots_alive() {
        Heap::init();
        let mut a = Gc::new(1);
        let mut owner = TCellOwner::new();
        unsafe { Heap::root(&mut a, &mut owner) };
        Heap::rooted(|gc| gc.sweep(&owner));
        assert_eq!(*a, 1);
    }

    #[cfg(feature = "gc_sanitize")]
    #[test]
    fn gc_sweep_keeps_roots_alive_twice() {
        Heap::init();
        let mut a = Gc::new(1);
        let mut owner = TCellOwner::new();
        unsafe { Heap::root(&mut a, &mut owner) };
        Heap::rooted(|gc| gc.sweep(&owner));
        Heap::rooted(|gc| gc.sweep(&owner));
        assert_eq!(*a, 1);
    }

    #[cfg(feature = "gc_sanitize")]
    #[test]
    #[should_panic]
    fn gc_sweep_frees_unmarked() {
        Heap::init();
        let a = Gc::new(1);
        let mut owner = TCellOwner::new();
        Heap::rooted(|gc| gc.sweep(&owner));
        assert_eq!(*a, 1); // should panic
    }

    #[cfg(feature = "gc_sanitize")]
    #[test]
    #[should_panic]
    fn gc_sweep_traverses_one() {
        Heap::init();
        let a = Gc::new(1);
        let b = Gc::new(2);
        let mut owner = TCellOwner::new();
        a.mark(&owner);
        Heap::rooted(|gc| gc.sweep(&owner));
        assert_eq!(*a, 1);
        assert_eq!(*b, 2); // should panic
    }

    #[cfg(feature = "gc_sanitize")]
    #[test]
    fn gc_sweep_unlinks() {
        Heap::init();
        let a = Gc::new(1);
        let b = Gc::new(2);
        let mut owner = TCellOwner::new();
        b.mark(&owner);
        Heap::rooted(|gc| gc.sweep(&owner));
        b.mark(&owner);
        Heap::rooted(|gc| gc.sweep(&owner));
        assert_eq!(*b, 2);
    }

    #[cfg(feature = "gc_sanitize")]
    #[test]
    fn gc_sweep_unlinks_two() {
        Heap::init();
        let a = Gc::new(1);
        let b = Gc::new(2);
        let c = Gc::new(3);
        let mut owner = TCellOwner::new();
        a.mark(&owner);
        c.mark(&owner);
        Heap::rooted(|gc| gc.sweep(&owner));
        c.mark(&owner);
        Heap::rooted(|gc| gc.sweep(&owner));
        c.mark(&owner);
        Heap::rooted(|gc| gc.sweep(&owner));
        assert_eq!(*c, 3);
    }
}
