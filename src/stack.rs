use std::ops::{Deref, DerefMut};
#[cfg(feature = "skip_vec")]
use std::ops::{Index, IndexMut};

use crate::vm::LBoxed;

use memmap2::{MmapMut, Advice};

const VALUE_STACK_DEFAULT: usize = 0x1000 * 0x1000 * 2; // 2mb hugepage

// The stack stores NuN-boxed values (`LBoxed`).
#[repr(C)]
pub struct ValueStack<'src, 'intern> {
    pub stack_ptr: core::ptr::NonNull<[LBoxed<'src, 'intern>]>,
    // `pub(crate)` so the JIT can address the live length with dynasm's typed
    // offset (`=> ValueStack.used`) when computing native arg/return slices.
    pub(crate) used: usize,
    mmap: MmapMut,
}

impl<'src, 'intern> Deref for ValueStack<'src, 'intern> {
    type Target = [LBoxed<'src, 'intern>];
    fn deref(&self) -> &Self::Target {
        unsafe { self.stack_ptr.get_unchecked_mut(..self.used).as_ref() }
    }
}

impl<'src, 'intern> DerefMut for ValueStack<'src, 'intern> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.stack_ptr.get_unchecked_mut(..self.used).as_mut() }
    }
}

#[cfg(feature = "skip_vec")]
impl<'src, 'intern, Idx: std::slice::SliceIndex<[LBoxed<'src, 'intern>]>> Index<Idx> for ValueStack<'src, 'intern> {
    type Output = Idx::Output;

    fn index(&self, index: Idx) -> &Self::Output {
        // safety: haha
        unsafe { self.stack_ptr.get_unchecked_mut(index).as_ref() }
    }
}

#[cfg(feature = "skip_vec")]
impl<'src, 'intern, Idx: std::slice::SliceIndex<[LBoxed<'src, 'intern>]>> IndexMut<Idx> for ValueStack<'src, 'intern> {
    fn index_mut(&mut self, index: Idx) -> &mut <Self as Index<Idx>>::Output {
        // safety: smile emoji
        unsafe { self.stack_ptr.get_unchecked_mut(index).as_mut() }
    }
}



impl<'src, 'intern> ValueStack<'src, 'intern> {
    pub fn new(capacity: usize) -> Self {
        let length = capacity * std::mem::size_of::<LBoxed<'src, 'intern>>();
        let mut mmap = MmapMut::map_anon(length).expect("ValueStack mmap succeeds");
        drop(mmap.advise(Advice::HugePage)); // Ignore if we can't madvise for a hugepage
        let stack_ptr = core::ptr::NonNull::new(mmap.as_mut_ptr() as *mut LBoxed<'src, 'intern>).expect("mmap succeeded which means its non-null");
        Self {
            stack_ptr: core::ptr::NonNull::slice_from_raw_parts(stack_ptr, capacity),
            used: 0,
            mmap,
        }
    }

    pub fn truncate(&mut self, new_len: usize) {
        // `LBoxed` is `Copy` with no `Drop`, so shrinking is just a length change.
        if new_len < self.used {
            self.used = new_len;
        }
    }

    pub fn extend_from_slice(&mut self, slice: &[LBoxed<'src, 'intern>]) {
        let new_len = self.used + slice.len();
        if new_len > self.mmap.len() / std::mem::size_of::<LBoxed<'src, 'intern>>() {
            panic!("ValueStack overflow");
        }
        for (i, val) in slice.iter().enumerate() {
            unsafe {
                std::ptr::write(self.stack_ptr.as_non_null_ptr().add(self.used + i).as_ptr(), *val);
            }
        }
        self.used = new_len;
    }

    pub fn resize_with<F>(&mut self, new_len: usize, mut f: F)
    where
        F: Fn() -> LBoxed<'src, 'intern>,
    {
        if new_len > self.used {
            self.extend_from_slice(vec![f(); new_len - self.used].as_slice());
        } else {
            self.truncate(new_len);
        }
    }

    pub fn last(&self) -> Option<&LBoxed<'src, 'intern>> {
        if self.used == 0 {
            None
        } else {
            Some(&self[self.used - 1])
        }
    }

    pub fn len(&self) -> usize {
        self.used
    }
}

impl<'src, 'intern> std::fmt::Debug for ValueStack<'src, 'intern> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        unsafe { std::slice::from_raw_parts(self.stack_ptr.as_non_null_ptr().as_ptr(), self.used).fmt(f) }
    }
}

impl<'src, 'intern> core::convert::From<Vec<LBoxed<'src, 'intern>>> for ValueStack<'src, 'intern> {
    fn from(mut value: Vec<LBoxed<'src, 'intern>>) -> Self {
        let mut new_stack = Self::new(VALUE_STACK_DEFAULT);
        new_stack.extend_from_slice(value.as_slice());
        new_stack
    }
}
