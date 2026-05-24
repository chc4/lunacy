use std::ops::Deref;
use crate::vm::{Tc, TcOwner, LValue, LClosure, Table, Gc};
use crate::TCellOwner;
pub trait Mark {
    fn mark(&self, owner: &TCellOwner<TcOwner>);
}

impl<'src, 'intern> Mark for LValue<'src, 'intern> {
    fn mark(&self, owner: &TCellOwner<TcOwner>) {
        match self {
            LValue::Nil => { },
            x => panic!("not implemented for {x:?}"),
        }
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

impl<T: Mark> Mark for Gc<T> {
    fn mark(&self, owner: &TCellOwner<TcOwner>) {
        self.borrow().mark(owner)
    }
}
