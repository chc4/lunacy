// Holes as absolute symbols (`hole.ll`): built by `just absolute-hole-experiment`
// as a PIE with cross-language ThinLTO, to see whether LLVM makes each hole an
// immediate operand of the arithmetic using it, and what relocation marks it.

unsafe extern "C" {
    fn hole1_u32() -> u32;
    fn hole1_u64() -> u64;
    fn hole2_u32() -> u32;
}

#[inline(never)]
#[unsafe(no_mangle)]
pub fn ex_sub_hole(x: u32) -> u32 {
    x.wrapping_sub(unsafe { hole1_u32() })
}

#[inline(never)]
#[unsafe(no_mangle)]
pub fn ex_and_hole(x: u64) -> u64 {
    x & unsafe { hole1_u64() }
}

#[inline(never)]
#[unsafe(no_mangle)]
pub fn ex_add_small_hole(x: u32) -> u32 {
    x.wrapping_add(unsafe { hole2_u32() })
}

#[inline(never)]
#[unsafe(no_mangle)]
pub fn ex_cmp_hole(x: u32) -> bool {
    x < unsafe { hole1_u32() }
}

fn main() {
    let x = std::hint::black_box(1000);
    println!("{} {} {} {}", ex_sub_hole(x), ex_and_hole(x as u64), ex_add_small_hole(x), ex_cmp_hole(x));
}
