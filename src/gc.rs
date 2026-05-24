use std::ops::Deref;
use std::collections::HashMap;
use std::sync::atomic::{Ordering, AtomicBool, AtomicPtr};
use crate::vm::{Tc, TcOwner, LValue, LClosure, Table};
use crate::{TCell, TCellOwner};
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
            x => panic!("not implemented for {x:?}"),
        }
    }
}

impl<T> Mark for Tc<T> {
    default fn mark(&self, owner: &TCellOwner<TcOwner>) {
    }
}

impl<T: Mark> Mark for Tc<T> {
    fn mark(&self, owner: &TCellOwner<TcOwner>) {
        self.ro(owner).mark(owner)
    }
}

impl<'src, 'intern> Mark for Table<'src, 'intern> {
    fn mark(&self, owner: &TCellOwner<TcOwner>) {
        for item in &self.array {
            item.mark(owner);
        }
        for (key, val) in &self.hash {
            key.mark(owner);
            val.mark(owner);
        }
    }
}

impl<'src, 'intern> Mark for LClosure<'src, 'intern> {
    fn mark(&self, owner: &TCellOwner<TcOwner>) {
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

struct Gc<T> {
    ptr: core::ptr::NonNull<GcInner<T>>,
}

impl<T> Mark for Gc<T> {
    default fn mark(&self, owner: &TCellOwner<TcOwner>) {
        // A Gc<T> object can only be marked if it is reachable by the mutator, and is only freed
        // by Heap::sweep if it unreachable and thus wasn't marked before the last sweep.
        unsafe { (*self.ptr.as_ptr()).state = ALIVE.load(Ordering::Acquire) };
    }
}

impl<T: Mark> Mark for Gc<T> {
    fn mark(&self, owner: &TCellOwner<TcOwner>) {
        // Safety: See default implementation.
        unsafe {
            (*self.ptr.as_ptr()).state = ALIVE.load(Ordering::Acquire);
            (*self.ptr.as_ptr()).val.mark(owner);
        };
    }
}

struct GcInner<T> {
    next: *mut GcInner<()>,
    state: bool,
    val: T,
}

static HEAP: AtomicPtr<*mut Heap> = AtomicPtr::new(core::ptr::null_mut());
#[derive(Default)]
pub struct Heap {
    top: *mut GcInner<()>,
    roots: HashMap<Gc<()>, usize>,
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
    unsafe fn sweep(&mut self, owner: &TCellOwner<TcOwner>) {
        // Mark all of our rooted objects.
        for (root, _) in &self.roots {
            unsafe { root.mark(owner) };
        }
        let alive = ALIVE.load(Ordering::Acquire);
        let mut prev = None;
        let mut current = self.top;
        while current != core::ptr::null_mut() {
            debug!("sweeping {current:p}");
            prev = Some(current);
            current = unsafe { (*current).next };
        }
        // Flip all live objects back to dead
        ALIVE.store(!alive, Ordering::Release);
    }
}
