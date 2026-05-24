use std::ops::Deref;
use std::collections::HashMap;
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

static ALIVE: TCell<TcOwner, bool> = TCell::new(true);

struct Gc<T> {
    ptr: core::ptr::NonNull<GcInner<T>>,
}

impl<T> Mark for Gc<T> {
    default fn mark(&self, owner: &TCellOwner<TcOwner>) {
        // A Gc<T> object can only be marked if it is reachable by the mutator, and is only freed
        // by Heap::sweep if it unreachable and thus wasn't marked before the last sweep.
        unsafe { (*self.ptr.as_ptr()).state = *ALIVE.ro(owner) };
    }
}

impl<T: Mark> Mark for Gc<T> {
    fn mark(&self, owner: &TCellOwner<TcOwner>) {
        // Safety: See default implementation.
        unsafe {
            (*self.ptr.as_ptr()).state = *ALIVE.ro(owner);
            (*self.ptr.as_ptr()).val.mark(owner);
        };
    }
}

struct GcInner<T> {
    next: *mut GcInner<()>,
    state: bool,
    val: T,
}

struct Heap {
    top: *mut GcInner<()>,
    roots: HashMap<Gc<()>, usize>,
}

impl Heap {
    /// Sweep all allocation and free unmarked objects.
    /// SAFETY: All reachable objects must be marked before being called, and any
    /// objects that haven't been marked must not be used afterwards.
    unsafe fn sweep(&mut self, owner: &mut TCellOwner<TcOwner>) {
        // Mark all of our rooted objects.
        for (root, _) in &self.roots {
            unsafe { root.mark(owner) };
        }
        let alive = *ALIVE.ro(owner);
        let mut prev = None;
        let mut current = self.top;
        while current != core::ptr::null_mut() {
            debug!("sweeping {current:p}");
            prev = Some(current);
            current = unsafe { (*current).next };
        }
        // Flip all live objects to dead
        *ALIVE.rw(owner) = !alive;
    }
}
