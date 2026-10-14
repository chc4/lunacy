//! Ops on the register window whose code is the JIT's own instructions, on registers the
//! allocator picks freely. See Note [Emitted ops].

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use dynasmrt::mmap::{ExecutableBuffer, MutableBuffer};
use dynasmrt::{dynasm, DynamicLabel, DynasmApi, DynasmLabelApi};
use smallvec::SmallVec;

use crate::lboxed::LBoxed;
use crate::vm::RunState;
use crate::window::Access;

// Note [Emitted ops]
// ~~~~~~~~~~~~~~~~~~
// An emitted op is an op on the register window whose code is a few instructions the JIT
// appends itself, rather than a stencil copied at a run of the window (Note [Register window]):
// its operands may be in any registers, so the allocator places each where it already is, and no
// shuffle brings them into a run. It declares its operands as a window op does, each boxed in a
// window register or a double unboxed in its paired XMM register (Note [Unboxed doubles]), and
// its code appends instructions given each operand's machine register. Besides its operands'
// registers it may use rax, r10 and xmm15, which hold nothing across an op. Operands of one slot
// are all of one form, as the window holds a slot's value in one place.
//
// The interpreter runs the same instructions: a standalone function, assembled once for each op
// and its constants, loads its inputs from an array into registers, runs the op's code, and
// stores its outputs to another. The interpreter unboxes and boxes the values on the way, as the
// JIT's window does at the stack, so either runs the op on the same unboxed values.

/// The assembler emitted ops append their code to.
pub type Assembler = dynasmrt::VecAssembler<dynasmrt::x64::X64Relocation>;

/// Where an emitted op's code goes on besides falling off its end, which is exit 0: its second
/// exit, and its cold path. See Note [Window exits].
pub struct Exits {
    pub exit1: DynamicLabel,
    pub cold: DynamicLabel,
}

/// An emitted op's cold path's code: a function, so that it captures nothing, its constants
/// loaded through its site's record. See Note [Emitted ops].
pub type Cold = fn(&mut Assembler, &[u8], &Record);

/// The site's record a cold path runs with, its address in r10: where each exit goes, then each
/// capture's value's displacement from it. See Note [Cold stencils].
pub struct Record;

impl Record {
    /// Load capture `capture`'s value into general register `reg`, through rax.
    pub fn capture(&self, ops: &mut Assembler, capture: usize, reg: u8) {
        let at = (2 * 8 + 4 * capture) as i32;
        dynasm!(ops
            ; .arch x64
            ; movsxd rax, DWORD [r10 + at]
            ; mov Rq(reg), QWORD [r10 + rax]
        );
    }

    /// Go on where the record has exit `exit` go.
    pub fn exit(&self, ops: &mut Assembler, exit: usize) {
        dynasm!(ops ; .arch x64 ; jmp QWORD [r10 + (exit * 8) as i32]);
    }
}

/// An op the JIT lays out as its own instructions, as `emitted!` declares one. See Note [Emitted
/// ops].
pub trait Emitted: std::fmt::Debug {
    /// Its type's name, which with its captures is what its code depends on, its operands'
    /// registers apart.
    fn name(&self) -> &'static str;
    /// Its name and captures, for dumps.
    fn label(&self) -> String;
    /// The operands' stack slots, relative to the frame's base, in the order the op declares
    /// them.
    fn operands(&self) -> &[usize];
    /// How the op uses each operand.
    fn accesses(&self) -> &'static [Access];
    /// The operands it takes and gives as unboxed doubles, in XMM registers: bit `i` for operand
    /// `i`.
    fn doubles(&self) -> u8;
    /// Its captures' values, in the order it declares them.
    fn captures(&self) -> SmallVec<[u64; 2]>;
    /// Whether it selects an exit: it has a second, or a cold path. See Note [Window exits].
    fn selects(&self) -> bool;
    /// Append its code to `ops`, operand `i` in machine register `regs[i]`: XMM for an unboxed
    /// double, general otherwise.
    fn emit(&self, ops: &mut Assembler, regs: &[u8], exits: &Exits);
    /// Its cold path's code, if it has one.
    fn cold(&self) -> Option<Cold>;
    /// The same op on `operands` in place of its own.
    fn with_operands(&self, operands: &[usize]) -> Rc<dyn Emitted>;
}

impl std::fmt::Display for dyn Emitted {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.label())?;
        for (slot, access) in self.operands().iter().zip(self.accesses()) {
            match access {
                Access::Write => write!(f, ", out {slot}")?,
                _ => write!(f, ", {slot}")?,
            }
        }
        Ok(())
    }
}

/// Declare an emitted op, as `windowed!` declares a window op:
///
/// `emitted!([select] Name, [captures], [const params], |ops, exits| (operands) { code } [cold |record| { code }])`
///
/// Its captures are its constants, by name and type; its const parameters are the type's. Its
/// operands are declared as a window op's: each by name, read unless `out`, boxed unless `f64`,
/// in the order the code takes them. The code appends the op's instructions to `ops`, each
/// operand's name its machine register (a `u8` for `Rq` or `Rx`, as its form says) and each
/// capture's name its value; it goes on at exit 0 by falling off its end, and jumps to
/// `exits.exit1` for its second exit, which a `select` op has, or `exits.cold` for its cold path.
/// A cold path's code is a function of the same registers, each capture's name its index in the
/// site's record, which `record` loads it from, and it goes on through `record.exit`. The op is a
/// struct of its captures and operands' slots, made by `Name::<params>::new(captures.., &[slots])`.
/// See Note [Emitted ops].
macro_rules! emitted {
    (select $name:ident, [$($cap:ident : $cty:ty),* $(,)?], [$($cp:ident : $cpt:ty),* $(,)?], |$ops:ident, $exits:ident| ($($operands:tt)*) $body:block) => {
        $crate::emitted::emitted!(@sort [$name, [$($cap : $cty),*], [$($cp : $cpt),*], |$ops, $exits| $body, true, []] [] $($operands)*);
    };
    (select $name:ident, [$($cap:ident : $cty:ty),* $(,)?], [$($cp:ident : $cpt:ty),* $(,)?], |$ops:ident, $exits:ident| ($($operands:tt)*) $body:block cold |$record:ident| $cold:block) => {
        $crate::emitted::emitted!(@sort [$name, [$($cap : $cty),*], [$($cp : $cpt),*], |$ops, $exits| $body, true, [|$record| $cold]] [] $($operands)*);
    };
    ($name:ident, [$($cap:ident : $cty:ty),* $(,)?], [$($cp:ident : $cpt:ty),* $(,)?], |$ops:ident, $exits:ident| ($($operands:tt)*) $body:block cold |$record:ident| $cold:block) => {
        $crate::emitted::emitted!(@sort [$name, [$($cap : $cty),*], [$($cp : $cpt),*], |$ops, $exits| $body, true, [|$record| $cold]] [] $($operands)*);
    };
    ($name:ident, [$($cap:ident : $cty:ty),* $(,)?], [$($cp:ident : $cpt:ty),* $(,)?], |$ops:ident, $exits:ident| ($($operands:tt)*) $body:block) => {
        $crate::emitted::emitted!(@sort [$name, [$($cap : $cty),*], [$($cp : $cpt),*], |$ops, $exits| $body, false, []] [] $($operands)*);
    };
    // Its cold path's code, each operand's name its register and each capture's its index in the
    // record.
    (@cold_code [] $ops:ident [$($op:ident)*] [$($cap:ident)*]) => {};
    (@cold_code [|$record:ident| $cold:block] $ops:ident [$($op:ident)*] [$($cap:ident)*]) => {
        /// Its cold path's code. See Note [Emitted ops].
        fn cold_code($ops: &mut $crate::emitted::Assembler, regs: &[u8], $record: &$crate::emitted::Record) {
            let mut regs = regs.iter().copied();
            $(let $op = regs.next().expect("a register for each of an emitted op's operands");)*
            let mut capture = 0usize;
            $(let $cap = capture; capture += 1; let _ = $cap;)*
            let _ = capture;
            $cold
        }
    };
    // Its cold path's code, if it has one.
    (@cold []) => { None };
    (@cold [|$record:ident| $cold:block]) => { Some(Self::cold_code as $crate::emitted::Cold) };
    (@sort $decl:tt [$($acc:tt)*] out f64 $op:ident $(, $($rest:tt)*)?) => {
        $crate::emitted::emitted!(@sort $decl [$($acc)* ($op, Write, true)] $($($rest)*)?);
    };
    (@sort $decl:tt [$($acc:tt)*] f64 $op:ident $(, $($rest:tt)*)?) => {
        $crate::emitted::emitted!(@sort $decl [$($acc)* ($op, Read, true)] $($($rest)*)?);
    };
    (@sort $decl:tt [$($acc:tt)*] out $op:ident $(, $($rest:tt)*)?) => {
        $crate::emitted::emitted!(@sort $decl [$($acc)* ($op, Write, false)] $($($rest)*)?);
    };
    (@sort $decl:tt [$($acc:tt)*] $op:ident $(, $($rest:tt)*)?) => {
        $crate::emitted::emitted!(@sort $decl [$($acc)* ($op, Read, false)] $($($rest)*)?);
    };
    (@sort
        [$name:ident, [$($cap:ident : $cty:ty),*], [$($cp:ident : $cpt:ty),*], |$ops:ident, $exits:ident| $body:block, $selects:literal, [$(|$record:ident| $cold:block)?]]
        [$(($op:ident, $access:ident, $double:literal))*]
    ) => {
        #[derive(Debug, Clone)]
        struct $name<$(const $cp: $cpt),*> {
            $($cap: $cty,)*
            operands: [usize; [$(stringify!($op)),*].len()],
        }

        impl<$(const $cp: $cpt),*> $name<$($cp),*> {
            fn new($($cap: $cty,)* operands: &[usize]) -> Self {
                $name { $($cap,)* operands: operands.try_into().expect("a slot for each of an emitted op's operands") }
            }

            $crate::emitted::emitted!(@cold_code [$(|$record| $cold)?] $ops [$($op)*] [$($cap)*]);
        }

        impl<$(const $cp: $cpt),*> $crate::emitted::Emitted for $name<$($cp),*> {
            fn name(&self) -> &'static str {
                std::any::type_name::<Self>()
            }
            fn label(&self) -> String {
                let mut label = String::from(stringify!($name));
                $(label.push_str(&format!(" {:?}", $cp));)*
                $(label.push_str(&format!(" {:?}", self.$cap));)*
                label
            }
            fn operands(&self) -> &[usize] {
                &self.operands
            }
            fn accesses(&self) -> &'static [$crate::window::Access] {
                &[$($crate::window::Access::$access),*]
            }
            fn doubles(&self) -> u8 {
                let forms: &[bool] = &[$($double),*];
                forms.iter().enumerate().fold(0, |bits, (i, &double)| bits | u8::from(double) << i)
            }
            fn captures(&self) -> smallvec::SmallVec<[u64; 2]> {
                smallvec::smallvec![$($crate::window::Capture::to_bits(self.$cap)),*]
            }
            fn selects(&self) -> bool {
                $selects
            }
            fn emit(&self, $ops: &mut $crate::emitted::Assembler, regs: &[u8], $exits: &$crate::emitted::Exits) {
                $(let $cap = self.$cap;)*
                let mut regs = regs.iter().copied();
                $(let $op = regs.next().expect("a register for each of an emitted op's operands");)*
                let _ = $exits;
                $body
            }
            fn cold(&self) -> Option<$crate::emitted::Cold> {
                $crate::emitted::emitted!(@cold [$(|$record| $cold)?])
            }
            fn with_operands(&self, operands: &[usize]) -> std::rc::Rc<dyn $crate::emitted::Emitted> {
                std::rc::Rc::new($name::<$($cp),*> { operands: operands.try_into().expect("a slot for each of an emitted op's operands"), ..self.clone() })
            }
        }
    };
}
pub(crate) use emitted;

/// A standalone's signature: the inputs, in the order the op declares them; where its outputs
/// go, likewise; and its site's record. It returns the exit it took.
type Standalone = unsafe extern "sysv64" fn(*const u64, *mut u64, *const u8) -> u64;

/// The general registers a standalone loads boxed inputs into: none the call passes pointers in,
/// nor an op's scratch.
const STANDALONE_REGS: [u8; 5] = [1 /* rcx */, 2 /* rdx */, 8 /* r8 */, 9 /* r9 */, 11 /* r11 */];

/// An op's standalone, and the offsets in it of where each exit goes. See Note [Emitted ops].
struct Standing {
    exec: ExecutableBuffer,
    exits: [usize; 2],
}

thread_local! {
    /// Each op's standalone, by its name and captures. See Note [Emitted ops].
    static STANDALONES: RefCell<HashMap<(&'static str, SmallVec<[u64; 2]>), Standing>> = RefCell::new(HashMap::new());
}

/// Assemble `op`'s standalone: the pinned tag set, the record's address kept, each input from the
/// array the first argument points to into a register of its own, the op's code, and each exit
/// storing each output to the array the second points to and returning its number. Its cold path
/// follows, the record's address in r10 as its code wants. See Note [Emitted ops].
fn standalone(op: &dyn Emitted) -> Standing {
    let mut ops = Assembler::new(0);
    let (mut xmms, mut gps) = (0u8, 0usize);
    let mut regs: SmallVec<[u8; 8]> = SmallVec::new();
    for i in 0..op.operands().len() {
        if op.doubles() >> i & 1 == 1 {
            regs.push(xmms);
            xmms += 1;
        } else {
            regs.push(STANDALONE_REGS[gps]);
            gps += 1;
        }
    }
    assert!(xmms < 8, "a standalone's XMM registers past the window's");
    // r14 is callee-saved, and the pinned tag in JIT code. See Note [Pinned tag].
    dynasm!(ops
        ; .arch x64
        ; push r14
        ; push rdx
        ; mov r14, QWORD LBoxed::NUMBER_TAG as i64
    );
    let mut input = 0;
    for (i, access) in op.accesses().iter().enumerate() {
        if access.reads() {
            let disp = input * 8;
            if op.doubles() >> i & 1 == 1 {
                dynasm!(ops ; .arch x64 ; vmovq Rx(regs[i]), QWORD [rdi + disp]);
            } else {
                dynasm!(ops ; .arch x64 ; mov Rq(regs[i]), QWORD [rdi + disp]);
            }
            input += 1;
        }
    }
    let exits = Exits { exit1: ops.new_dynamic_label(), cold: ops.new_dynamic_label() };
    op.emit(&mut ops, &regs, &exits);
    let exit0 = ops.new_dynamic_label();
    dynasm!(ops ; .arch x64 ; =>exit0);
    for (exit, label) in [(0, exit0), (1, exits.exit1)] {
        if exit == 1 {
            dynasm!(ops ; .arch x64 ; =>label);
        }
        let mut output = 0;
        for (i, access) in op.accesses().iter().enumerate() {
            if access.writes() {
                let disp = output * 8;
                if op.doubles() >> i & 1 == 1 {
                    dynasm!(ops ; .arch x64 ; vmovq QWORD [rsi + disp], Rx(regs[i]));
                } else {
                    dynasm!(ops ; .arch x64 ; mov QWORD [rsi + disp], Rq(regs[i]));
                }
                output += 1;
            }
        }
        dynasm!(ops
            ; .arch x64
            ; add rsp, 8
            ; pop r14
            ; mov eax, exit
            ; ret
        );
    }
    dynasm!(ops ; .arch x64 ; =>exits.cold);
    match op.cold() {
        Some(cold) => {
            dynasm!(ops ; .arch x64 ; mov r10, QWORD [rsp]);
            cold(&mut ops, &regs, &Record);
        }
        None => dynasm!(ops ; .arch x64 ; ud2),
    }
    let offsets = [exit0, exits.exit1].map(|label| ops.labels().resolve_dynamic(label).expect("a standalone's exit").0);
    let code = ops.finalize().expect("a standalone's code");
    let mut buf = MutableBuffer::new(code.len()).expect("memory for a standalone");
    buf.set_len(code.len());
    buf[..].copy_from_slice(&code);
    Standing { exec: buf.make_exec().expect("an executable standalone"), exits: offsets }
}

/// Run `op` on the running frame's stack slots, as the interpreter does: its standalone on its
/// inputs, unboxed as it takes them, with a record of its own, and its outputs boxed back. An op
/// that selects selects the exit it took. See Note [Emitted ops].
pub fn interp(op: &dyn Emitted, state: &mut RunState<'_, '_>) {
    let mut inputs: SmallVec<[u64; 8]> = SmallVec::new();
    for (i, (&slot, access)) in op.operands().iter().zip(op.accesses()).enumerate() {
        if access.reads() {
            let bits = state.vals[state.base + slot].bits();
            inputs.push(if op.doubles() >> i & 1 == 1 { bits.wrapping_sub(LBoxed::DOUBLE_ENCODE_OFFSET) } else { bits });
        }
    }
    let mut outputs = [0u64; 8];
    let exit = STANDALONES.with_borrow_mut(|standalones| {
        let standing = standalones.entry((op.name(), op.captures())).or_insert_with(|| standalone(op));
        let base = standing.exec.as_ptr() as u64;
        // The record: where each exit goes, each capture's value's displacement from it, then the
        // values. See Note [Cold stencils].
        let captures = op.captures();
        let at = (2 * 8 + 4 * captures.len()).next_multiple_of(8);
        let mut record = vec![0u8; at + 8 * captures.len()];
        for (exit, &offset) in standing.exits.iter().enumerate() {
            record[exit * 8..exit * 8 + 8].copy_from_slice(&(base + offset as u64).to_le_bytes());
        }
        for (i, &value) in captures.iter().enumerate() {
            let disp = (at + 8 * i) as i32;
            record[16 + 4 * i..20 + 4 * i].copy_from_slice(&disp.to_le_bytes());
            record[at + 8 * i..at + 8 * i + 8].copy_from_slice(&value.to_le_bytes());
        }
        // SAFETY: the standalone reads as many inputs as the op has and writes as many outputs.
        let f: Standalone = unsafe { core::mem::transmute(standing.exec.as_ptr()) };
        unsafe { f(inputs.as_ptr(), outputs.as_mut_ptr(), record.as_ptr()) }
    });
    if op.selects() {
        state.select = exit as usize;
    }
    let mut output = 0;
    for (i, (&slot, access)) in op.operands().iter().zip(op.accesses()).enumerate() {
        if access.writes() {
            let bits = outputs[output];
            // SAFETY: an unboxed output is a double the op computed from boxed numbers. See Note
            // [Arithmetic NaNs].
            state.vals[state.base + slot] = if op.doubles() >> i & 1 == 1 {
                unsafe { LBoxed::from_arith(f64::from_bits(bits)) }
            } else {
                unsafe { LBoxed::from_bits(bits) }
            };
            output += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    emitted!(Sub, [], [], |ops, exits| (f64 a, f64 b, out f64 out) {
        dynasm!(ops ; .arch x64 ; vsubsd Rx(out), Rx(a), Rx(b));
    });

    // `out := a + k`, its overflow's cold path `out := k`, from the record, at exit 1.
    emitted!(AddK, [k: i32], [], |ops, exits| (a, out out) {
        dynasm!(ops
            ; .arch x64
            ; mov eax, Rd(a)
            ; add eax, k
            ; jo =>exits.cold
            ; mov Rq(out), rax
        );
    } cold |record| {
        record.capture(ops, k, out);
        record.exit(ops, 1);
    });

    /// Run `op`'s standalone on `inputs` with `captures` in its record: its outputs and its exit.
    fn run(op: &dyn Emitted, inputs: &[u64]) -> ([u64; 8], u64) {
        let standing = standalone(op);
        let base = standing.exec.as_ptr() as u64;
        let captures = op.captures();
        let at = (2 * 8 + 4 * captures.len()).next_multiple_of(8);
        let mut record = vec![0u8; at + 8 * captures.len()];
        for (exit, &offset) in standing.exits.iter().enumerate() {
            record[exit * 8..exit * 8 + 8].copy_from_slice(&(base + offset as u64).to_le_bytes());
        }
        for (i, &value) in captures.iter().enumerate() {
            record[16 + 4 * i..20 + 4 * i].copy_from_slice(&((at + 8 * i) as i32).to_le_bytes());
            record[at + 8 * i..at + 8 * i + 8].copy_from_slice(&value.to_le_bytes());
        }
        let f: Standalone = unsafe { core::mem::transmute(standing.exec.as_ptr()) };
        let mut out = [0u64; 8];
        let exit = unsafe { f(inputs.as_ptr(), out.as_mut_ptr(), record.as_ptr()) };
        (out, exit)
    }

    /// A standalone loads its inputs in the order the op declares them, runs its code on them,
    /// and stores its output.
    #[test]
    fn standalone_runs_the_op() {
        let values = [1.5, -2.25, 0.0, -0.0, 1e300, f64::INFINITY, 3.0];
        for &l in &values {
            for &r in &values {
                let (out, exit) = run(&Sub::new(&[0, 1, 2]), &[l.to_bits(), r.to_bits()]);
                let (got, want) = (f64::from_bits(out[0]), l - r);
                assert!(got.to_bits() == want.to_bits() || (got.is_nan() && want.is_nan()), "{l} - {r}");
                assert_eq!(exit, 0);
            }
        }
    }

    /// A standalone's cold path loads its constants through the record and goes on where it has
    /// its exit go.
    #[test]
    fn standalone_takes_its_cold_path() {
        let (out, exit) = run(&AddK::new(7, &[0, 1]), &[5]);
        assert_eq!((out[0] as u32, exit), (12, 0));
        let (out, exit) = run(&AddK::new(7, &[0, 1]), &[i32::MAX as u32 as u64]);
        assert_eq!((out[0] as u32, exit), (7, 1));
    }
}
