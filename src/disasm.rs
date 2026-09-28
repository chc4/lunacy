//! Disassembly of the JIT's code (feature `jit_disasm`), written to
//! `jit_disasm.txt` when the JIT context is dropped: every range of code it
//! committed (a region, a thunk stub), annotated with what emitted each part of
//! it (the region's entry, its blocks and their residuals, its exit and constant
//! pool) and with what its branches and immediates name: blocks, the JIT's
//! helpers, and any other function of the binary, from its symbol table.

use std::cell::RefCell;
use std::collections::HashMap;
use std::io::Write;

use yaxpeax_arch::LengthedInstruction;
use yaxpeax_x86::long_mode::{InstDecoder, Opcode, Operand, RegSpec};

/// A note that the bytes after it are the constant pool, which is data.
pub const POOL: &str = "constant pool";

/// A committed range of code, and the notes on it by offset.
struct Range {
    addr: usize,
    len: usize,
    title: String,
    notes: Vec<(usize, String)>,
}

#[derive(Default)]
pub struct Disasm {
    /// Notes on the code being assembled, by offset in it.
    notes: RefCell<Vec<(usize, String)>>,
    ranges: RefCell<Vec<Range>>,
}

impl Disasm {
    /// What the code assembled from `offset` on is.
    pub fn note(&self, offset: usize, note: String) {
        self.notes.borrow_mut().push((offset, note));
    }

    /// The code assembled, `len` bytes, is now at `addr`: it takes the notes
    /// made on it.
    pub fn committed(&self, addr: usize, len: usize, title: String) {
        let notes = std::mem::take(&mut *self.notes.borrow_mut());
        self.ranges.borrow_mut().push(Range { addr, len, title, notes });
    }

    /// Disassemble every range into `path`, naming the addresses in `named`.
    pub fn write(&self, path: &str, named: &HashMap<usize, String>) {
        let symbols = &Symbols { named, functions: functions() };
        let Ok(file) = std::fs::File::create(path) else { return };
        let mut out = std::io::BufWriter::new(file);
        let mut ranges = self.ranges.borrow_mut();
        ranges.sort_by_key(|range| range.addr);
        let decoder = InstDecoder::default();
        for range in ranges.iter() {
            writeln!(out, "==== {} @ {:#x}, {} bytes", range.title, range.addr, range.len).ok();
            // Safety: the JIT buffer holding the range is still mapped.
            let code = unsafe { std::slice::from_raw_parts(range.addr as *const u8, range.len) };
            let mut notes = range.notes.iter().peekable();
            let mut data = false;
            let mut off = 0;
            while off < code.len() {
                while let Some((_, note)) = notes.next_if(|(at, _)| *at <= off) {
                    writeln!(out, "  ; {note}").ok();
                    data |= note == POOL;
                }
                let addr = range.addr + off;
                if data {
                    let end = (off + 8).min(code.len());
                    let mut bytes = [0u8; 8];
                    bytes[..end - off].copy_from_slice(&code[off..end]);
                    let value = u64::from_le_bytes(bytes) as usize;
                    writeln!(out, "  {addr:12x} +{off:<5x} .quad {value:#x}{}", name(symbols, value).map(|s| format!("  ; {s}")).unwrap_or_default()).ok();
                    off = end;
                    continue;
                }
                let Ok(inst) = decoder.decode_slice(&code[off..]) else {
                    writeln!(out, "  {addr:12x} +{off:<5x} .byte {:#04x}", code[off]).ok();
                    off += 1;
                    continue;
                };
                let end = off + inst.len().to_const() as usize;
                let bytes: String = code[off..end].iter().map(|b| format!("{b:02x}")).collect();
                let mut comment = Vec::new();
                for i in 0..inst.operand_count() {
                    match inst.operand(i) {
                        Operand::ImmediateI8 { imm } if relative(inst.opcode()) => comment.push(target(symbols, range, range.addr + end, imm as isize)),
                        Operand::ImmediateI32 { imm } if relative(inst.opcode()) => comment.push(target(symbols, range, range.addr + end, imm as isize)),
                        Operand::ImmediateI64 { imm } => comment.extend(name(symbols, imm as usize)),
                        Operand::ImmediateU64 { imm } => comment.extend(name(symbols, imm as usize)),
                        Operand::Disp { base, disp } if base == RegSpec::RIP => {
                            let slot = (range.addr + end).wrapping_add(disp as isize as usize);
                            // A load from the region's constant pool: its value.
                            if slot >= range.addr && slot + 8 <= range.addr + range.len {
                                let value = unsafe { std::ptr::read_unaligned(slot as *const usize) };
                                comment.push(format!("[{slot:#x}] = {value:#x}{}", name(symbols, value).map(|s| format!(" {s}")).unwrap_or_default()));
                            } else {
                                comment.push(format!("[{slot:#x}]"));
                            }
                        }
                        _ => {}
                    }
                }
                let comment = if comment.is_empty() { String::new() } else { format!("  ; {}", comment.join(", ")) };
                writeln!(out, "  {addr:12x} +{off:<5x} {bytes:<30} {inst}{comment}").ok();
                off = end;
            }
            writeln!(out).ok();
        }
    }
}

/// Each stencil the JIT copied, from its address, `SKIP` and the body it
/// splats (`window::stencil_body`), written to `path`: the stencil function's
/// bytes and instructions, and the body's, biggest body first. For `just
/// stencil-sizes`.
pub fn write_stencils<'a>(path: &str, copied: impl Iterator<Item = (usize, usize, &'a crate::window::Body)>) {
    let functions = functions();
    let function = |addr: usize| functions.iter().find(|f| f.0 == addr);
    let mut rows: Vec<(usize, usize, usize, usize, String)> = copied
        .map(|(addr, skip, body)| {
            let (size, name) = function(addr).map(|(_, size, name)| (*size, name.clone())).unwrap_or((0, format!("{addr:#x}")));
            // Safety: the stencil is a function of this executable, `size` long.
            let code = unsafe { std::slice::from_raw_parts(addr as *const u8, size) };
            (instructions(&body.code), body.code.len(), instructions(code), size, format!("{name} at SKIP {skip}"))
        })
        .collect();
    rows.sort_by(|a, b| b.cmp(a));
    let Ok(file) = std::fs::File::create(path) else { return };
    let mut out = std::io::BufWriter::new(file);
    writeln!(out, "{:>13} {:>13}", "copied body", "function").ok();
    writeln!(out, "{:>6} {:>6} {:>6} {:>6}  stencil", "insts", "bytes", "insts", "bytes").ok();
    for (insts, bytes, fn_insts, fn_bytes, name) in rows {
        writeln!(out, "{insts:>6} {bytes:>6} {fn_insts:>6} {fn_bytes:>6}  {name}").ok();
    }
}

/// How many instructions `code` decodes to.
fn instructions(code: &[u8]) -> usize {
    let decoder = InstDecoder::default();
    let (mut off, mut count) = (0, 0);
    while let Ok(inst) = decoder.decode_slice(&code[off..]) {
        off += inst.len().to_const() as usize;
        count += 1;
        if off >= code.len() {
            break;
        }
    }
    count
}

/// Whether the opcode's first operand is a relative branch target.
fn relative(opcode: Opcode) -> bool {
    crate::window::RELATIVE_BRANCHES.contains(&opcode)
}

/// Names for addresses: those given, and the binary's functions.
struct Symbols<'a> {
    named: &'a HashMap<usize, String>,
    /// (address, size, demangled name), by address.
    functions: Vec<(usize, usize, String)>,
}

/// The binary's functions, from its symbol table, at their addresses in this
/// process (as `window::Image` finds them).
fn functions() -> Vec<(usize, usize, String)> {
    let Ok(file) = std::fs::File::open("/proc/self/exe") else { return Vec::new() };
    // Safety: nothing writes our own executable while it runs.
    let Ok(bytes) = (unsafe { memmap2::Mmap::map(&file) }) else { return Vec::new() };
    let Ok(elf) = goblin::elf::Elf::parse(&bytes) else { return Vec::new() };
    let Some(anchor) = elf.syms.iter().find(|s| elf.strtab.get_at(s.st_name) == Some("__lunacy_window_anchor")) else { return Vec::new() };
    let bias = (crate::window::__lunacy_window_anchor as *const () as usize).wrapping_sub(anchor.st_value as usize);
    let mut functions: Vec<(usize, usize, String)> = elf
        .syms
        .iter()
        .filter(|s| s.is_function() && s.st_size != 0)
        .filter_map(|s| {
            let name = elf.strtab.get_at(s.st_name)?;
            Some((bias.wrapping_add(s.st_value as usize), s.st_size as usize, format!("{:#}", rustc_demangle::demangle(name))))
        })
        .collect();
    functions.sort_by_key(|f| f.0);
    functions
}

/// What is at `addr`: a block or helper, or a function of the binary (and how
/// far into it), if any.
fn name(symbols: &Symbols, addr: usize) -> Option<String> {
    if let Some(name) = symbols.named.get(&addr) {
        return Some(name.clone());
    }
    let i = symbols.functions.partition_point(|f| f.0 <= addr).checked_sub(1)?;
    let (start, size, name) = &symbols.functions[i];
    (addr < start + size).then(|| if addr == *start { name.clone() } else { format!("{name}+{:#x}", addr - start) })
}

/// A branch target, `disp` from `next`: what is there, else its offset in the
/// range or its address.
fn target(symbols: &Symbols, range: &Range, next: usize, disp: isize) -> String {
    let addr = next.wrapping_add(disp as usize);
    if let Some(name) = name(symbols, addr) {
        format!("-> {name}")
    } else if (range.addr..range.addr + range.len).contains(&addr) {
        format!("-> +{:#x}", addr - range.addr)
    } else {
        format!("-> {addr:#x}")
    }
}
