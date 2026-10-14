//! Ops on the register window whose code is the JIT's own instructions, on registers the
//! allocator picks freely. See Note [Emitted ops].

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use dynasmrt::mmap::{ExecutableBuffer, MutableBuffer};
use dynasmrt::{dynasm, DynasmApi};
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

/// An op the JIT lays out as its own instructions, as `emitted!` declares one. See Note [Emitted
/// ops].
pub trait Emitted: std::fmt::Debug {
    fn name(&self) -> &'static str;
    /// Its name and constants, for dumps.
    fn label(&self) -> String;
    /// The operands' stack slots, relative to the frame's base, in the order the op declares
    /// them.
    fn operands(&self) -> &[usize];
    /// How the op uses each operand.
    fn accesses(&self) -> &'static [Access];
    /// The operands it takes and gives as unboxed doubles, in XMM registers: bit `i` for operand
    /// `i`.
    fn doubles(&self) -> u8;
    /// Its constants, which with its name are what its code depends on, its operands' registers
    /// apart.
    fn constants(&self) -> SmallVec<[u64; 2]>;
    /// Append its code to `ops`, operand `i` in machine register `regs[i]`: XMM for an unboxed
    /// double, general otherwise.
    fn emit(&self, ops: &mut Assembler, regs: &[u8]);
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

/// Declare an emitted op: `emitted!(Name, [captures], |ops| (operands) { code })`. Its captures
/// are its constants, by name and type. Its operands are declared as a window op's (`windowed!`):
/// each by name, read unless `out`, boxed unless `f64`, in the order the code's ops take them.
/// The code appends the op's instructions to `ops`, each operand's name its machine register, a
/// `u8` for `Rq` or `Rx` as its form says, and each capture's name its value. The op is a struct
/// of its captures and operands' slots, made by `Name::new(captures.., &[slots])`. See Note
/// [Emitted ops].
macro_rules! emitted {
    (
        $(#[$meta:meta])*
        $name:ident,
        [$($cap:ident : $cty:ty),* $(,)?],
        |$ops:ident| ($($operands:tt)*)
        $body:block
    ) => {
        $crate::emitted::emitted!(@sort [$(#[$meta])* $name, [$($cap : $cty),*], |$ops| $body] [] $($operands)*);
    };
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
        [$(#[$meta:meta])* $name:ident, [$($cap:ident : $cty:ty),*], |$ops:ident| $body:block]
        [$(($op:ident, $access:ident, $double:literal))*]
    ) => {
        $(#[$meta])*
        #[derive(Debug, Clone)]
        struct $name {
            $($cap: $cty,)*
            operands: [usize; [$(stringify!($op)),*].len()],
        }

        impl $name {
            fn new($($cap: $cty,)* operands: &[usize]) -> Self {
                $name { $($cap,)* operands: operands.try_into().expect("a slot for each of an emitted op's operands") }
            }
        }

        impl $crate::emitted::Emitted for $name {
            fn name(&self) -> &'static str {
                stringify!($name)
            }
            fn label(&self) -> String {
                let mut label = String::from(stringify!($name));
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
            fn constants(&self) -> smallvec::SmallVec<[u64; 2]> {
                smallvec::smallvec![$($crate::window::Capture::to_bits(self.$cap)),*]
            }
            fn emit(&self, $ops: &mut $crate::emitted::Assembler, regs: &[u8]) {
                $(let $cap = self.$cap;)*
                let mut regs = regs.iter().copied();
                $(let $op = regs.next().expect("a register for each of an emitted op's operands");)*
                $body
            }
            fn with_operands(&self, operands: &[usize]) -> std::rc::Rc<dyn $crate::emitted::Emitted> {
                std::rc::Rc::new($name { operands: operands.try_into().expect("a slot for each of an emitted op's operands"), ..self.clone() })
            }
        }
    };
}
pub(crate) use emitted;

/// A standalone's signature: the inputs, in the order the op declares them, then where its
/// outputs go, likewise.
type Standalone = unsafe extern "sysv64" fn(*const u64, *mut u64);

/// The general registers a standalone loads boxed inputs into: none the call passes pointers in,
/// nor an op's scratch.
const STANDALONE_REGS: [u8; 5] = [1 /* rcx */, 2 /* rdx */, 8 /* r8 */, 9 /* r9 */, 11 /* r11 */];

thread_local! {
    /// Each op's standalone, by its name and constants. See Note [Emitted ops].
    static STANDALONES: RefCell<HashMap<(&'static str, SmallVec<[u64; 2]>), ExecutableBuffer>> = RefCell::new(HashMap::new());
}

/// Assemble `op`'s standalone: each input from the array the first argument points to into a
/// register of its own, the op's code, and each output to the array the second points to.
fn standalone(op: &dyn Emitted) -> ExecutableBuffer {
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
    assert!(xmms < 15, "a standalone's XMM registers past its scratch");
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
    op.emit(&mut ops, &regs);
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
    dynasm!(ops ; .arch x64 ; ret);
    let code = ops.finalize().expect("a standalone's code");
    let mut buf = MutableBuffer::new(code.len()).expect("memory for a standalone");
    buf.set_len(code.len());
    buf[..].copy_from_slice(&code);
    buf.make_exec().expect("an executable standalone")
}

/// Run `op` on the running frame's stack slots, as the interpreter does: its standalone on its
/// inputs, unboxed as it takes them, and its outputs boxed back. See Note [Emitted ops].
pub fn interp(op: &dyn Emitted, state: &mut RunState<'_, '_>) {
    let mut inputs: SmallVec<[u64; 8]> = SmallVec::new();
    for (i, (&slot, access)) in op.operands().iter().zip(op.accesses()).enumerate() {
        if access.reads() {
            let bits = state.vals[state.base + slot].bits();
            inputs.push(if op.doubles() >> i & 1 == 1 { bits.wrapping_sub(LBoxed::DOUBLE_ENCODE_OFFSET) } else { bits });
        }
    }
    let mut outputs = [0u64; 8];
    STANDALONES.with_borrow_mut(|standalones| {
        let exec = standalones.entry((op.name(), op.constants())).or_insert_with(|| standalone(op));
        // SAFETY: the standalone reads as many inputs as the op has and writes as many outputs.
        let f: Standalone = unsafe { core::mem::transmute(exec.as_ptr()) };
        unsafe { f(inputs.as_ptr(), outputs.as_mut_ptr()) };
    });
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

    emitted!(Sub, [], |ops| (f64 a, f64 b, out f64 out) {
        dynasm!(ops ; .arch x64 ; vsubsd Rx(out), Rx(a), Rx(b));
    });

    /// A standalone loads its inputs in the order the op declares them, runs its code on them,
    /// and stores its output.
    #[test]
    fn standalone_runs_the_op() {
        let values = [1.5, -2.25, 0.0, -0.0, 1e300, f64::INFINITY, 3.0];
        let exec = standalone(&Sub::new(&[0, 1, 2]));
        let f: Standalone = unsafe { core::mem::transmute(exec.as_ptr()) };
        for &l in &values {
            for &r in &values {
                let inputs = [l.to_bits(), r.to_bits()];
                let mut out = [0u64; 8];
                unsafe { f(inputs.as_ptr(), out.as_mut_ptr()) };
                let (got, want) = (f64::from_bits(out[0]), l - r);
                assert!(got.to_bits() == want.to_bits() || (got.is_nan() && want.is_nan()), "{l} - {r}");
            }
        }
    }
}
