//! Proves `Heap::reset` (run at the end of `Vm::scope`) actually frees the objects allocated
//! during the scope, rather than leaking them. A counting global allocator records
//! deallocations; we allocate a batch of GC objects, then assert `reset` deallocates them.
//!
//! Only meaningful without `gc_sanitize`: that feature deliberately leaks objects (marking
//! them dead instead of freeing) so the sanitizer can catch use-after-free.
#![cfg(not(feature = "gc_sanitize"))]

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};

use lunacy::gc::{Gc, Heap};

static DEALLOCS: AtomicUsize = AtomicUsize::new(0);

struct Counting;
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 { unsafe { System.alloc(l) } }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        DEALLOCS.fetch_add(1, Ordering::Relaxed);
        unsafe { System.dealloc(p, l) }
    }
}

#[global_allocator]
static ALLOC: Counting = Counting;

#[test]
fn reset_frees_scope_allocations() {
    Heap::init();
    const N: usize = 1000;
    // Each Gc::new boxes a GcInner and links it onto the heap's `top` list.
    for i in 0..N {
        let _ = Gc::new(i as u64);
    }
    assert_eq!(Heap::live_bytes() > 0, true, "allocations should be tracked live");

    let before = DEALLOCS.load(Ordering::Relaxed);
    Heap::reset();
    let freed = DEALLOCS.load(Ordering::Relaxed) - before;

    assert!(
        freed >= N,
        "reset deallocated {freed} blocks, expected at least {N} (the scope's GcInners) — a leak",
    );
    assert_eq!(Heap::live_bytes(), 0, "reset should zero tracked live bytes");
}
