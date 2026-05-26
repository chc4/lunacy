use std::ops::{Deref, DerefMut};
use std::hash::Hash;
use std::rc::Rc;
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
        for item in &self.array {
            item.mark(owner);
        }
        self.hash.mark(owner);
    }
}

impl<'src, 'intern> Mark for LClosure<'src, 'intern> {
    fn mark(&self, owner: &TCellOwner<TcOwner>) {
        for upval in &self.upvalues {
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

static ALIVE: AtomicBool = AtomicBool::new(true);

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
        let heap = unsafe { HEAP.load(Ordering::Acquire).as_ref().unwrap() };
        let mut top = heap.top.load(Ordering::Acquire);
        let inner = GcInner {
            next: AtomicPtr::new(top),
            state: !ALIVE.load(Ordering::Acquire),
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
            match heap.top.compare_exchange(top, erased, Ordering::Acquire, Ordering::Relaxed) {
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
        Self { ptr: core::ptr::NonNull::new(ptr as _).unwrap() }
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
    fn mark(&self, owner: &TCellOwner<TcOwner>) {
        // SAFETY: See default implementation.
        unsafe {
            let state = &mut (*self.ptr.as_ptr()).state;
            let alive = ALIVE.load(Ordering::Acquire);
            if *state != alive {
                *state = alive;
                (*self.ptr.as_ptr()).val.mark(owner);
            }
        };
    }
}

struct GcInner<T: ?Sized> {
    next: AtomicPtr<GcInner<()>>,
    finalize: fn(*mut GcInner<()>),
    state: bool,
    #[cfg(feature = "gc_sanitize")]
    alive: AtomicBool,
    val: T,
}

static HEAP: AtomicPtr<Heap> = AtomicPtr::new(core::ptr::null_mut());
#[derive(Default)]
pub struct Heap {
    top: AtomicPtr<GcInner<()>>,
    roots: BTreeMap<*const (), (Box<dyn Mark>, usize)>,
}

impl Heap {
    pub fn init() {
        if HEAP.load(Ordering::Acquire) == core::ptr::null_mut() {
            let heap = Box::leak(Default::default());
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

    /// Sweep all allocation and free unmarked objects.
    /// SAFETY: All reachable objects must be marked before being called, and any
    /// objects that haven't been marked must not be used afterwards.
    pub unsafe fn sweep(owner: &TCellOwner<TcOwner>) {
        let heap = unsafe { HEAP.load(Ordering::Acquire).as_mut().unwrap() };
        // Mark all of our rooted objects.
        for (_ptr, (tr, _)) in &heap.roots {
            tr.mark(owner);
        }
        let alive = ALIVE.load(Ordering::Acquire);
        let mut prev = &raw mut heap.top;
        let mut current = heap.top.load(Ordering::Acquire);
        while current != core::ptr::null_mut() {
            let next_ptr = unsafe { (*current).next.load(Ordering::Acquire) };
            if unsafe { (*current).state } != alive {
                debug!("freeing {current:p}");
                unsafe { (*prev).store(next_ptr, Ordering::Release) };
                unsafe { ((*current).finalize)(current.cast()) };
            } else {
                prev = unsafe { &raw mut (*current).next };
            }
            current = next_ptr;
        }
        // Flip all live objects back to dead
        ALIVE.store(!alive, Ordering::Release);
    }

    pub unsafe fn collect(state: &impl Mark, owner: &TCellOwner<TcOwner>) {
        state.mark(owner);
        unsafe { Self::sweep(owner) };
    }

    /// Root a GC pointer, so that it is automatically marked by the GC before any sweep.
    /// The caller is required to guarantee that GC object is unrooted before freeing
    /// it, and that the root doesn't outlive any lifetimes attached to the object.
    // TODO: Replace with Root smartpointer instead.
    pub unsafe fn root<T: Mark>(gc: &mut Gc<T>, owner: &mut TCellOwner<TcOwner>) {
        // SAFETY: We have owner. Maybe still kinda sus think about this some more
        let heap = unsafe { HEAP.load(Ordering::Acquire).as_mut().unwrap() };
        // Increment the root count for this key
        let ptr = gc.ptr.as_ptr();
        let dt: Box<Gc<T>> = Box::new(gc.clone());
        // SAFETY: Erase the lifetime of Gc<T>. The caller is required to not have the
        // object remain rooted longer than its lifetimes.
        let dt: Box<dyn Mark> = unsafe { core::mem::transmute(dt as Box<dyn Mark>) };
        heap.roots.entry(ptr.cast()).or_insert_with(|| (dt, 0)).1 += 1;
    }

    fn unroot<T>(gc: &Gc<T>, owner: &mut TCellOwner<TcOwner>) {
        // No-op for now?
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
        unsafe { Heap::sweep(&owner) };
    }

    #[cfg(feature = "gc_sanitize")]
    #[test]
    fn gc_sweep_keeps_marks_alive() {
        Heap::init();
        let a = Gc::new(1);
        let owner = TCellOwner::new();
        a.mark(&owner);
        unsafe { Heap::sweep(&owner) };
        assert_eq!(*a, 1);
    }

    #[cfg(feature = "gc_sanitize")]
    #[test]
    fn gc_sweep_keeps_marks_alive_twice() {
        Heap::init();
        let a = Gc::new(1);
        let owner = TCellOwner::new();
        a.mark(&owner);
        unsafe { Heap::sweep(&owner) };
        a.mark(&owner);
        unsafe { Heap::sweep(&owner) };
        assert_eq!(*a, 1);
    }

    #[cfg(feature = "gc_sanitize")]
    #[test]
    fn gc_sweep_keeps_roots_alive() {
        Heap::init();
        let mut a = Gc::new(1);
        let mut owner = TCellOwner::new();
        unsafe { Heap::root(&mut a, &mut owner) };
        unsafe { Heap::sweep(&owner) };
        assert_eq!(*a, 1);
    }

    #[cfg(feature = "gc_sanitize")]
    #[test]
    fn gc_sweep_keeps_roots_alive_twice() {
        Heap::init();
        let mut a = Gc::new(1);
        let mut owner = TCellOwner::new();
        unsafe { Heap::root(&mut a, &mut owner) };
        unsafe { Heap::sweep(&owner) };
        unsafe { Heap::sweep(&owner) };
        assert_eq!(*a, 1);
    }

    #[cfg(feature = "gc_sanitize")]
    #[test]
    #[should_panic]
    fn gc_sweep_frees_unmarked() {
        Heap::init();
        let a = Gc::new(1);
        let mut owner = TCellOwner::new();
        unsafe { Heap::sweep(&owner) };
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
        unsafe { Heap::sweep(&owner) };
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
        unsafe { Heap::sweep(&owner) };
        b.mark(&owner);
        unsafe { Heap::sweep(&owner) };
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
        unsafe { Heap::sweep(&owner) };
        c.mark(&owner);
        unsafe { Heap::sweep(&owner) };
        c.mark(&owner);
        unsafe { Heap::sweep(&owner) };
        assert_eq!(*c, 3);
    }
}
