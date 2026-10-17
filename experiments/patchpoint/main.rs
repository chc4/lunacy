//! Stencil-hole experiment (`just patchpoint-experiment`): does an LLVM
//! patchpoint, written in IR (hole.ll) and inlined into Rust by cross-language
//! LTO, give a stencil hole that is an immediate in the instruction stream
//! rather than a RIP-relative load?
//!
//! Each `ex_*` function is one shape of `x - hole` (the integer windows'
//! arithmetic), so the disassembly of the site can be compared directly:
//! * `ex_baseline`: today's hole, an `extern_weak` static read through the GOT
//!   with the same `asm!` barrier as `window::hole`;
//! * `ex_anyreg`, `ex_anyreg_two`, `ex_anyreg_small`: an anyregcc patchpoint;
//! * `ex_ccc`: a C-convention patchpoint;
//! * `ex_asm_imm`: no patchpoint, an `asm!` `mov r32, imm32` placeholder whose
//!   immediate's offset is recorded in a section of its own;
//! * `ex_stackmap`: a stackmap recording where an operand lives.
#![feature(linkage)]

use std::hint::black_box;

unsafe extern "C" {
    fn pp_anyreg0() -> u64;
    fn pp_anyreg1() -> u64;
    fn pp_anyreg_small() -> u64;
    fn pp_ccc0() -> u64;
    fn sm_record(x: u64);

    #[linkage = "extern_weak"]
    static __lunacy_hole0: *const ();
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn ex_baseline(x: u32) -> u32 {
    let mut value = unsafe { __lunacy_hole0 as u64 };
    unsafe { core::arch::asm!("/* hole {0} */", inout(reg) value, options(pure, nomem, nostack, preserves_flags)) };
    x.wrapping_sub(value as u32)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn ex_anyreg(x: u32) -> u32 {
    x.wrapping_sub(unsafe { pp_anyreg0() } as u32)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn ex_anyreg_two(x: u32, y: u32) -> u32 {
    let a = x.wrapping_sub(unsafe { pp_anyreg0() } as u32);
    let b = y.wrapping_add(unsafe { pp_anyreg1() } as u32);
    a ^ b
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn ex_anyreg_small(x: u32) -> u32 {
    x.wrapping_sub(unsafe { pp_anyreg_small() } as u32)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn ex_ccc(x: u32, y: u32) -> u32 {
    // `y` is live across the site, to show what a call-like site costs.
    let a = x.wrapping_sub(unsafe { pp_ccc0() } as u32);
    a ^ y
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn ex_asm_imm(x: u32) -> u32 {
    let value: u32;
    // The immediate is the last 4 bytes of the instruction; label 2 marks its
    // end, so the patch offset is `2b - 4`, recorded (PC-relative) in `.lunacy_imm_holes`.
    unsafe {
        core::arch::asm!(
            "mov {0:e}, 0x7eadbeef",
            "2:",
            ".pushsection .lunacy_imm_holes,\"aR\",@progbits",
            ".long 2b - 4 - .",
            ".popsection",
            out(reg) value,
            options(pure, nomem, nostack, preserves_flags),
        )
    };
    x.wrapping_sub(value)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn ex_stackmap(x: u64) -> u64 {
    let y = x.wrapping_mul(3);
    unsafe { sm_record(y) };
    y.wrapping_add(1)
}

// ---- patching the sites, as a copy&patch JIT would ---------------------------

unsafe extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut u8;
    static __ehdr_start: u8;
}

fn u16_at(b: &[u8], o: usize) -> u16 { u16::from_le_bytes(b[o..o + 2].try_into().unwrap()) }
fn u32_at(b: &[u8], o: usize) -> u32 { u32::from_le_bytes(b[o..o + 4].try_into().unwrap()) }
fn u64_at(b: &[u8], o: usize) -> u64 { u64::from_le_bytes(b[o..o + 8].try_into().unwrap()) }

/// `.llvm_stackmaps` as loaded (so its function addresses are relocated): its
/// link-time address and size from this executable's section headers, plus the
/// load bias (`__ehdr_start` is the image's first byte, at vaddr 0 under PIE).
fn stackmaps() -> &'static [u8] {
    let elf = std::fs::read("/proc/self/exe").unwrap();
    let (shoff, shentsize, shnum, shstrndx) =
        (u64_at(&elf, 0x28) as usize, u16_at(&elf, 0x3a) as usize, u16_at(&elf, 0x3c) as usize, u16_at(&elf, 0x3e) as usize);
    let sh = |i: usize| &elf[shoff + i * shentsize..];
    let strtab = u64_at(sh(shstrndx), 0x18) as usize;
    for i in 0..shnum {
        let name = &elf[strtab + u32_at(sh(i), 0) as usize..];
        if name.starts_with(b".llvm_stackmaps\0") {
            let (addr, size) = (u64_at(sh(i), 0x10) as usize, u64_at(sh(i), 0x20) as usize);
            let bias = unsafe { &__ehdr_start as *const u8 as usize };
            return unsafe { std::slice::from_raw_parts((bias + addr) as *const u8, size) };
        }
    }
    panic!("no .llvm_stackmaps section");
}

/// One stackmap record: the function it is in, its ID, the site's offset in the
/// function, and its locations' (type, DWARF register).
struct Site { function: usize, id: u64, offset: u32, locations: Vec<(u8, u16)> }

/// Stackmap format version 3 (LLVM's StackMaps documentation).
fn sites(map: &[u8]) -> Vec<Site> {
    assert_eq!(map[0], 3, "stackmap version");
    let (nfun, nconst) = (u32_at(map, 4) as usize, u32_at(map, 8) as usize);
    let mut functions = Vec::new();
    for f in 0..nfun {
        let o = 16 + f * 24;
        functions.push((u64_at(map, o) as usize, u64_at(map, o + 16) as usize));
    }
    let mut o = 16 + nfun * 24 + nconst * 8;
    let mut out = Vec::new();
    for (function, count) in functions {
        for _ in 0..count {
            let (id, offset, nloc) = (u64_at(map, o), u32_at(map, o + 8), u16_at(map, o + 14) as usize);
            o += 16;
            let mut locations = Vec::new();
            for _ in 0..nloc {
                locations.push((map[o], u16_at(map, o + 4)));
                o += 12;
            }
            o = (o + 7) & !7;
            let nlive = u16_at(map, o + 2) as usize;
            o = (o + 4 + nlive * 4 + 7) & !7;
            out.push(Site { function, id, offset, locations });
        }
    }
    out
}

/// x86 register number of a DWARF register number.
fn x86_reg(dwarf: u16) -> u8 {
    [0, 2, 1, 3, 6, 7, 5, 4, 8, 9, 10, 11, 12, 13, 14, 15][dwarf as usize]
}

/// Copy `len` bytes of `f` (position-independent: these functions make no
/// RIP-relative references) into fresh executable memory, and write
/// `mov r32, imm` over each of its patchpoints' reserved bytes, `r` being the
/// register the stackmap records for the result, and nops over the rest of
/// them. `values` is (ID, reserved bytes, value): the stackmap does not record
/// how many bytes a patchpoint reserved, only the IR does.
fn copy_and_patch(f: usize, len: usize, values: &[(u64, usize, u32)]) -> usize {
    let mem = unsafe { mmap(std::ptr::null_mut(), 4096, 7, 0x22, -1, 0) };
    assert!(!mem.is_null() && mem as isize != -1);
    let code = unsafe { std::slice::from_raw_parts_mut(mem, len) };
    code.copy_from_slice(unsafe { std::slice::from_raw_parts(f as *const u8, len) });
    for site in sites(stackmaps()).iter().filter(|s| s.function == f) {
        let &(_, reserved, value) = values.iter().find(|(id, _, _)| *id == site.id).unwrap();
        let (kind, dwarf) = site.locations[0];
        assert_eq!(kind, 1, "result location is a register");
        let r = x86_reg(dwarf);
        let mut insn = Vec::new();
        if r >= 8 { insn.push(0x41) }
        insn.push(0xb8 + (r & 7));
        insn.extend_from_slice(&value.to_le_bytes());
        let at = site.offset as usize;
        println!("  patched id {} at +{:#x}: mov {}, {:#x} ({} bytes), then {} nops", site.id, at, ["eax","ecx","edx","ebx","esp","ebp","esi","edi","r8d","r9d","r10d","r11d","r12d","r13d","r14d","r15d"][r as usize], value, insn.len(), reserved - insn.len());
        assert!(insn.len() <= reserved);
        insn.resize(reserved, 0x90);
        code[at..at + reserved].copy_from_slice(&insn);
    }
    mem as usize
}

fn main() {
    let x = black_box(1000u32);
    println!("unpatched (the reserved bytes are nops; results are whatever the register held):");
    println!("ex_baseline      {}", ex_baseline(x));
    println!("ex_anyreg        {}", ex_anyreg(x));
    println!("ex_anyreg_two    {}", ex_anyreg_two(x, x));
    println!("ex_anyreg_small  {}", ex_anyreg_small(x));
    println!("ex_ccc           {}", ex_ccc(x, x));
    println!("ex_asm_imm       {}", ex_asm_imm(x));
    println!("ex_stackmap      {}", ex_stackmap(x as u64));

    println!("stackmap records:");
    for s in sites(stackmaps()) {
        println!("  id {} in fn {:#x} at +{:#x}, locations {:?}", s.id, s.function, s.offset, s.locations);
    }

    println!("copy&patch ex_anyreg with hole = 7:");
    let f: fn(u32) -> u32 = unsafe { std::mem::transmute(copy_and_patch(ex_anyreg as *const () as usize, 32, &[(100, 10, 7)])) };
    let r = f(x);
    println!("  ex_anyreg'({x}) = {r}");
    assert_eq!(r, x - 7);
    println!("copy&patch ex_anyreg_small with hole = 40:");
    let f: fn(u32) -> u32 = unsafe { std::mem::transmute(copy_and_patch(ex_anyreg_small as *const () as usize, 16, &[(102, 6, 40)])) };
    let r = f(x);
    println!("  ex_anyreg_small'({x}) = {r}");
    assert_eq!(r, x - 40);
    println!("copy&patch ex_anyreg_two with holes 100 = 7, 101 = 5:");
    let f: fn(u32, u32) -> u32 = unsafe { std::mem::transmute(copy_and_patch(ex_anyreg_two as *const () as usize, 32, &[(100, 10, 7), (101, 10, 5)])) };
    let r = f(x, 2000);
    println!("  ex_anyreg_two'({x}, 2000) = {r}");
    assert_eq!(r, (x - 7) ^ (2000 + 5));
}
