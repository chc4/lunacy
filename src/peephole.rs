//! Fusing runs of integer arithmetic into one window op. See Note [Peephole fusion].

use std::rc::Rc;

use crate::lboxed::LBoxed;
use crate::vm::Opcode;
use crate::window::{windowed, Window};

// Note [Peephole fusion]
// ~~~~~~~~~~~~~~~~~~~~~~
// Each integer operation in the integer encoding checks its own result fits, and boxes it, though
// the next often only reads it to compute another: `(p - 1) % 256 + 1` checks and boxes three
// times. A run of integer operations can instead be one window op, which boxes once and has one
// cold path.
//
// Every generator's yields pass through a peephole as the specializer lays them out. An integer
// operation's generator says what its window computes before yielding it, and the peephole holds
// such a window instead of laying it out: the generator goes on as if it took its hot path, its
// result fitting, and so does the code after it, whichever instructions those are. What the
// peephole holds it lays out as soon as anything else would lay out code, or the next operation
// doesn't continue the run as a fused op could: what it holds has been read by nothing laid out
// since. Questions about types and constants, and guards known statically, lay out nothing, and
// pass it by.
//
// A fused op is a run of two or three operations of a register and a constant, each but the first
// reading the slot the one before wrote, all writing the same slot: adds, subtracts, products by a
// positive constant and masks (a floored remainder by a power of two). Its kinds are the op's
// constant parameters, so each step is inlined into the next, nothing boxed between them.
//
// A run of one operation is laid out as it would have been where it was held, its overflow
// continuing from there, and the code after it from its hot path again. A run of more is laid out
// as its fused op, an optimistic op of its own: on its hot path, the code goes on as it would after
// the run's last operation's hot path; on its cold path, the run's first operation is laid out as
// it would have been where it was held, and the code after it again from there, the run's inputs as
// they were.
//
// The fused op computes each step as its operation would, in the integer encoding, and takes its
// cold path where any step's result wouldn't fit, as the operation would take its own: it writes its
// slot only where every step fit. Its operations make no -0, so a step that fits is the double the
// operation would have computed.

/// An arithmetic operation of the integer encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Arith {
    Add,
    Sub,
    Mul,
    /// Floored, as Lua's `%`.
    Mod,
}

/// An operand: a slot holding an integer, or a constant.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Operand {
    Slot(usize),
    K(i32),
}

/// An integer operation writing `dest`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct IntOp {
    pub op: Arith,
    pub lhs: Operand,
    pub rhs: Operand,
    pub dest: usize,
}

impl IntOp {
    /// The integer operation an arithmetic opcode is, if it is one.
    pub fn of(opcode: Opcode, lhs: Operand, rhs: Operand, dest: usize) -> Option<Self> {
        let op = match opcode {
            Opcode::ADD => Arith::Add,
            Opcode::SUB => Arith::Sub,
            Opcode::MUL => Arith::Mul,
            Opcode::MOD => Arith::Mod,
            _ => return None,
        };
        Some(IntOp { op, lhs, rhs, dest })
    }

    /// Its step of a fused op, and the step's constant, if it is one: of a register and a
    /// constant, making no -0.
    fn step(&self) -> Option<(u8, i32)> {
        let (Operand::Slot(_), Operand::K(k)) = (self.lhs, self.rhs) else { return None };
        match self.op {
            Arith::Add => Some((ADD, k)),
            Arith::Sub => Some((SUB, k)),
            Arith::Mul if k > 0 => Some((MUL, k)),
            Arith::Mod if k > 0 && k & (k - 1) == 0 => Some((MASK, k - 1)),
            _ => None,
        }
    }
}

/// The most operations a fused op is.
pub const MAX_RUN: usize = 3;

/// Whether `op` can begin a run. See Note [Peephole fusion].
pub fn starts(op: &IntOp) -> bool {
    op.step().is_some()
}

/// Whether `op` goes on with `run` as a fused op could: one more step, reading the slot the run
/// writes and writing it again. See Note [Peephole fusion].
pub fn extends(run: &[IntOp], op: &IntOp) -> bool {
    let Some(last) = run.last() else { return starts(op) };
    run.len() < MAX_RUN && starts(op) && op.lhs == Operand::Slot(last.dest) && op.dest == last.dest
}

/// Whether integer operations are held to fuse (Note [Peephole fusion]); set `LUNACY_NO_FUSION`
/// for none, to compare.
pub fn fuses() -> bool {
    static FUSES: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var_os("LUNACY_NO_FUSION").is_none());
    *FUSES
}

// A fused op's steps, its constant parameters.
const ADD: u8 = 0;
const SUB: u8 = 1;
const MUL: u8 = 2;
/// `k` the mask.
const MASK: u8 = 3;

/// Step `S` of a fused op on `x`, with its constant `k`: its result, if it fits.
fn step<const S: u8>(x: i32, k: i32) -> Option<i32> {
    match S {
        ADD => x.checked_add(k),
        SUB => x.checked_sub(k),
        MUL => x.checked_mul(k),
        MASK => Some(x & k),
        _ => unreachable!(),
    }
}

/// Steps `A` and `B` of a fused op on `x`: the result, if every step's fits.
fn steps2<const A: u8, const B: u8>(x: i32, k1: i32, k2: i32) -> Option<i32> {
    step::<B>(step::<A>(x, k1)?, k2)
}

/// Steps `A`, `B` and `C` of a fused op on `x`: the result, if every step's fits.
fn steps3<const A: u8, const B: u8, const C: u8>(x: i32, k1: i32, k2: i32, k3: i32) -> Option<i32> {
    step::<C>(step::<B>(step::<A>(x, k1)?, k2)?, k3)
}

// Two steps: every step fits on the hot path; on the cold path, `dest` holds `lhs`, as nothing was
// computed. Its constants are whole holes, which a stencil reads as they are: decoding several
// narrower ones costs it masks. See Note [Peephole fusion].
windowed!(FusedRK2, [k1: u64, k2: u64], [A: u8, B: u8], |owner, state, base, tag| (lhs, out dest) {
    match steps2::<A, B>(lhs.as_int(), k1 as i32, k2 as i32) {
        Some(n) => { *dest = LBoxed::from_int_tagged(n, tag); false },
        None => { core::intrinsics::cold_path(); true },
    }
} cold {
    *dest = lhs;
    1
});

// Three steps, as `FusedRK2`.
windowed!(FusedRK3, [k1: u64, k2: u64, k3: u64], [A: u8, B: u8, C: u8], |owner, state, base, tag| (lhs, out dest) {
    match steps3::<A, B, C>(lhs.as_int(), k1 as i32, k2 as i32, k3 as i32) {
        Some(n) => { *dest = LBoxed::from_int_tagged(n, tag); false },
        None => { core::intrinsics::cold_path(); true },
    }
} cold {
    *dest = lhs;
    1
});

/// The step whose constant parameter is `$s`, as `$S` in `$body`.
macro_rules! by_step {
    ($s:expr, $S:ident, $body:expr) => {
        match $s {
            ADD => { const $S: u8 = ADD; $body },
            SUB => { const $S: u8 = SUB; $body },
            MUL => { const $S: u8 = MUL; $body },
            MASK => { const $S: u8 = MASK; $body },
            _ => unreachable!(),
        }
    };
}

/// The fused op a run is, if it is one. See Note [Peephole fusion].
pub fn fused_window(run: &[IntOp]) -> Option<Rc<dyn Window>> {
    let first = run.first()?;
    if !run.iter().enumerate().all(|(i, op)| extends(&run[..i], op)) {
        return None;
    }
    let Operand::Slot(lhs) = first.lhs else { return None };
    let slots = [lhs, first.dest];
    let steps: Vec<(u8, i32)> = run.iter().map(|op| op.step().unwrap()).collect();
    match steps.as_slice() {
        &[(a, k1), (b, k2)] => Some(by_step!(a, A, by_step!(b, B, Rc::new(FusedRK2::<A, B>::new(k1 as u32 as u64, k2 as u32 as u64, &slots)) as Rc<dyn Window>))),
        &[(a, k1), (b, k2), (c, k3)] => Some(by_step!(a, A, by_step!(b, B, by_step!(c, C, Rc::new(FusedRK3::<A, B, C>::new(k1 as u32 as u64, k2 as u32 as u64, k3 as u32 as u64, &slots)) as Rc<dyn Window>)))),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use Operand::{K, Slot};

    fn op(op: Arith, lhs: Operand, rhs: Operand, dest: usize) -> IntOp {
        IntOp { op, lhs, rhs, dest }
    }

    #[test]
    fn an_index_computation_is_a_fused_op() {
        // (p - 1) % 256 + 1, from slot 5 into slot 6, as uxn.lua computes a stack index.
        let run = [op(Arith::Sub, Slot(5), K(1), 6), op(Arith::Mod, Slot(6), K(256), 6), op(Arith::Add, Slot(6), K(1), 6)];
        assert!(run.iter().enumerate().all(|(i, o)| extends(&run[..i], o)));
        let window = fused_window(&run).expect("a fused op");
        assert_eq!(window.name(), "FusedRK3");
        assert_eq!(window.operands(), &[5, 6]);
    }

    #[test]
    fn what_a_run_extends_by() {
        let run = [op(Arith::Add, Slot(1), K(3), 2)];
        // Not reading the slot the run writes, or writing another.
        assert!(!extends(&run, &op(Arith::Add, Slot(1), K(3), 2)));
        assert!(!extends(&run, &op(Arith::Add, Slot(2), K(3), 3)));
        // Two registers; a product that could be -0; a remainder not a mask.
        assert!(!extends(&run, &op(Arith::Add, Slot(2), Slot(1), 2)));
        assert!(!extends(&run, &op(Arith::Mul, Slot(2), K(-2), 2)));
        assert!(!extends(&run, &op(Arith::Mod, Slot(2), K(7), 2)));
        assert!(extends(&run, &op(Arith::Mul, Slot(2), K(256), 2)));
        // At most three.
        let three = [run[0], op(Arith::Add, Slot(2), K(1), 2), op(Arith::Add, Slot(2), K(1), 2)];
        assert!(!extends(&three, &op(Arith::Add, Slot(2), K(1), 2)));
    }

    #[test]
    fn steps_compute_as_lua_does() {
        // Each step against Lua's doubles, on edge values: its result where that is an integer,
        // else none; masks for power-of-two remainders.
        let edges = [0, 1, -1, 255, 256, -256, i32::MAX, i32::MIN, 1 << 30, -(1 << 30)];
        for &x in &edges {
            for k in [1, 2, 7, 256, 65536, -3, i32::MAX] {
                for (kind, s) in [(Arith::Add, ADD), (Arith::Sub, SUB), (Arith::Mul, MUL)] {
                    let o = op(kind, Slot(0), K(k), 0);
                    if kind == Arith::Mul && k <= 0 {
                        continue;
                    }
                    assert_eq!(by_step!(s, S, step::<S>(x, k)), in_encoding(lua(&o, &[x as f64])), "{o:?} on {x}");
                }
            }
            for k in [1, 2, 256, 1 << 30] {
                let o = op(Arith::Mod, Slot(0), K(k), 0);
                assert_eq!(step::<MASK>(x, k - 1), in_encoding(lua(&o, &[x as f64])), "{o:?} on {x}");
            }
        }
    }

    /// A slot's value as Lua 5.1 computes it, in doubles.
    fn lua(op: &IntOp, slots: &[f64]) -> f64 {
        let v = |o: Operand| match o { K(k) => k as f64, Slot(s) => slots[s] };
        let (l, r) = (v(op.lhs), v(op.rhs));
        match op.op {
            Arith::Add => l + r,
            Arith::Sub => l - r,
            Arith::Mul => l * r,
            Arith::Mod => l - (l / r).floor() * r,
        }
    }

    /// Whether a double is a value of the integer encoding: whole, in range, and not -0.
    fn in_encoding(v: f64) -> Option<i32> {
        (v.fract() == 0.0 && v >= i32::MIN as f64 && v <= i32::MAX as f64 && v.to_bits() != (-0.0f64).to_bits()).then_some(v as i32)
    }

    #[test]
    fn runs_agree_with_lua_numbers() {
        // Random runs a fused op could be, on edge and random integers, against Lua's doubles: what
        // it writes, it writes as Lua computes it, and it writes nothing exactly where a step's
        // result, as Lua computes it, isn't an integer, where the operation would take its cold path.
        let mut seed = 0x9e3779b97f4a7c15u64;
        let mut rand = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let edges = [0, 1, -1, 2, 255, 256, -256, i32::MAX, i32::MIN, i32::MAX - 1, i32::MIN + 1, 1 << 30, -(1 << 30), 65535];
        let (mut fit, mut left) = (0, 0);
        for _ in 0..200_000 {
            let (src, dest) = ((rand() % 3) as usize, (rand() % 3) as usize);
            let mut run: Vec<IntOp> = Vec::new();
            for i in 0..(2 + rand() % 2) {
                let k = match rand() % 4 { 0 => edges[(rand() % edges.len() as u64) as usize], 1 => 1 << (rand() % 20), _ => (rand() % 600) as i32 - 300 };
                let kind = [Arith::Add, Arith::Sub, Arith::Mul, Arith::Mod][(rand() % 4) as usize];
                let candidate = op(kind, Slot(if i == 0 { src } else { dest }), K(k), dest);
                if extends(&run, &candidate) {
                    run.push(candidate);
                }
            }
            if run.len() < 2 {
                continue;
            }
            assert!(fused_window(&run).is_some(), "{run:?}");
            let inputs: Vec<i32> = (0..3).map(|_| match rand() % 3 {
                0 => edges[(rand() % edges.len() as u64) as usize],
                _ => (rand() % 2000) as i32 - 1000,
            }).collect();
            let mut expected: Vec<f64> = inputs.iter().map(|&v| v as f64).collect();
            let mut every_step_fits = true;
            for o in &run {
                expected[o.dest] = lua(o, &expected);
                every_step_fits &= in_encoding(expected[o.dest]).is_some();
            }
            // As the fused op computes it: its steps, from its one input.
            let Slot(from) = run[0].lhs else { unreachable!() };
            let result = run.iter().try_fold(inputs[from], |x, o| {
                let (s, k) = o.step().unwrap();
                by_step!(s, S, step::<S>(x, k))
            });
            match result {
                Some(n) => {
                    fit += 1;
                    assert!(every_step_fits, "{run:?} fused on {inputs:?}");
                    assert_eq!((n as f64).to_bits(), expected[dest].to_bits(), "{run:?} on {inputs:?}");
                },
                None => {
                    left += 1;
                    assert!(!every_step_fits, "{run:?} left on {inputs:?}");
                },
            }
        }
        assert!(fit > 1000 && left > 100, "fit {fit}, left {left}");
    }
}
