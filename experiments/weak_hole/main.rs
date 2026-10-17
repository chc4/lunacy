// A hole declared as the stencils declare theirs (`window.rs`): an `extern_weak`
// static whose address is the captured value. Built by `just weak-hole-experiment`
// under each relocation model, to see whether the address becomes an immediate
// operand and what relocation, if any, marks it in the linked executable.
#![feature(linkage)]

unsafe extern "C" {
    #[linkage = "extern_weak"]
    static __lunacy_hole1: *const ();
}

#[inline(never)]
#[unsafe(no_mangle)]
pub fn ex_sub_hole(x: u32) -> u32 {
    x.wrapping_sub(unsafe { __lunacy_hole1 } as u64 as u32)
}

#[inline(never)]
#[unsafe(no_mangle)]
pub fn ex_and_hole(x: u64) -> u64 {
    x & unsafe { __lunacy_hole1 } as u64
}

fn main() {
    let x = std::hint::black_box(1000);
    println!("{} {}", ex_sub_hole(x), ex_and_hole(x as u64));
}
