//! Fusing runs of integer arithmetic into one operation. See Note [Peephole fusion].

use std::rc::Rc;

use crate::lboxed::LBoxed;
use crate::specialize::ResidualExec;
use crate::vm::Opcode;

// Note [Peephole fusion]
// ~~~~~~~~~~~~~~~~~~~~~~
// Each integer operation in the integer encoding checks its own result fits, and boxes it, though
// the next often only reads it to compute another: `(p - 1) % 256 + 1` checks and boxes three
// times. A run of integer operations can instead be one operation, computing in 64 bits and
// checking once.
//
// Every generator's yields pass through a peephole as the specializer lays them out. An integer
// operation's generator says what its window computes before yielding it, and the peephole holds
// such a window instead of laying it out: the generator goes on as if it took its hot path, its
// result fitting, and so does the code after it, whichever instructions those are. What the
// peephole holds it lays out as soon as anything else would lay out code, or the next operation
// isn't one it can hold with them: what it holds has been read by nothing laid out since. Questions
// about types and constants, and guards known statically, lay out nothing, and pass it by.
//
// A run of one operation is laid out as it would have been where it was held, its overflow
// continuing from there, and the code after it from its hot path again. A run of two or more is
// laid out as one, guarded by whether its results fit: on the hot path the code goes on where the
// peephole laid it out; on the cold path, the run's first operation is laid out as it would have
// been where it was held, and the code after it again from there, the run's inputs as they were.
//
// The fused operation computes every result exactly: its operations neither make a -0 nor exceed
// 2^53 from integers, so 64-bit integers give what doubles would. It checks that each slot it
// writes, as the last of its operations to write the slot leaves it, fits the integer encoding,
// and only then writes them all: where one doesn't fit, it writes nothing. A slot only an earlier
// operation of the run writes, written again later in it, is never seen, and needs no check.

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

    /// Whether it can be fused: never one that could make a -0 (a product with a factor that
    /// isn't a positive constant) or divide by a slot.
    pub fn fusable(&self) -> bool {
        use Operand::{K, Slot};
        match (self.op, self.lhs, self.rhs) {
            (Arith::Add | Arith::Sub, _, _) => true,
            (Arith::Mul, Slot(_), K(k)) | (Arith::Mul, K(k), Slot(_)) => k > 0,
            (Arith::Mod, Slot(_), K(k)) => k > 0,
            _ => false,
        }
    }

    /// The operation of `l` and `r`, exactly.
    fn apply(&self, l: i64, r: i64) -> i64 {
        match self.op {
            Arith::Add => l + r,
            Arith::Sub => l - r,
            Arith::Mul => l * r,
            Arith::Mod => l.rem_euclid(r),
        }
    }

    /// The most the result's magnitude can be, given each operand's.
    fn bound(&self, l: u128, r: u128) -> u128 {
        match self.op {
            Arith::Add | Arith::Sub => l + r,
            Arith::Mul => l * r,
            // Of a positive constant divisor.
            Arith::Mod => r,
        }
    }
}

/// The most operations a run fuses.
pub const MAX_RUN: usize = 8;

/// Whether `ops`, run in order on integers, can be fused: at most `MAX_RUN` of them, each fusable,
/// and computing every result exactly, none past 2^53. See Note [Peephole fusion].
pub fn exact(ops: &[IntOp]) -> bool {
    let mut bounds: Vec<(usize, u128)> = Vec::new();
    let bound = |bounds: &Vec<(usize, u128)>, operand: Operand| match operand {
        Operand::K(k) => (k as i64).unsigned_abs() as u128,
        Operand::Slot(s) => bounds.iter().rev().find(|(w, _)| *w == s).map_or(1 << 31, |(_, b)| *b),
    };
    ops.len() <= MAX_RUN && ops.iter().all(|op| {
        let b = op.bound(bound(&bounds, op.lhs), bound(&bounds, op.rhs));
        bounds.push((op.dest, b));
        op.fusable() && b <= 1 << 53
    })
}

/// Whether integer operations are held to fuse (Note [Peephole fusion]); set `LUNACY_NO_FUSION`
/// for none, to compare.
pub fn fuses() -> bool {
    static FUSES: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var_os("LUNACY_NO_FUSION").is_none());
    *FUSES
}

/// A run of integer operations as one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fused {
    pub ops: Vec<IntOp>,
    /// The slots it writes, in the order the run first writes them.
    pub writes: Vec<usize>,
}

impl Fused {
    pub fn new(ops: Vec<IntOp>) -> Self {
        let mut writes = Vec::new();
        for op in &ops {
            if !writes.contains(&op.dest) {
                writes.push(op.dest);
            }
        }
        Fused { ops, writes }
    }

    /// Each slot it writes and the value it leaves there, from the slots' values before the run,
    /// as `read` gives them; or none, where one doesn't fit the integer encoding.
    pub fn eval(&self, read: impl Fn(usize) -> i32) -> Option<Vec<(usize, i32)>> {
        let mut written: Vec<(usize, i64)> = Vec::new();
        let value = |written: &Vec<(usize, i64)>, operand: Operand| match operand {
            Operand::K(k) => k as i64,
            // Read only where the run hasn't written it: a slot it has may hold anything before it.
            Operand::Slot(s) => written.iter().rev().find(|(w, _)| *w == s).map_or_else(|| read(s) as i64, |(_, v)| *v),
        };
        for op in &self.ops {
            let result = op.apply(value(&written, op.lhs), value(&written, op.rhs));
            written.push((op.dest, result));
        }
        self.writes.iter().map(|&slot| {
            let v = value(&written, Operand::Slot(slot));
            i32::try_from(v).ok().map(|v| (slot, v))
        }).collect()
    }

    /// It as a residual: it selects 0 having written its results, and 1 having written nothing.
    pub fn exec(self) -> ResidualExec {
        let writes = self.writes.clone();
        let fused = Rc::new(self);
        ResidualExec::new("fused", Rc::new(move |_owner, state| {
            let base = state.base;
            // Its inputs are in the integer encoding: it holds only integer paths.
            let results = fused.eval(|slot| unsafe { state.vals[base + slot].as_int() });
            state.select = match results {
                Some(results) => {
                    for (slot, n) in results {
                        state.vals[base + slot] = LBoxed::from_int(n);
                    }
                    0
                },
                None => 1,
            };
        })).writing(&writes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use Operand::{K, Slot};

    #[test]
    fn checks_only_what_the_run_leaves() {
        // 2^30 + 2^30 doesn't fit, but the run overwrites it before anything sees it.
        let ops = vec![IntOp { op: Arith::Add, lhs: Slot(0), rhs: Slot(0), dest: 1 }, IntOp { op: Arith::Sub, lhs: Slot(1), rhs: Slot(0), dest: 1 }];
        assert_eq!(Fused::new(ops.clone()).eval(|_| 1 << 30), Some(vec![(1, 1 << 30)]));
        assert_eq!(Fused::new(ops[..1].to_vec()).eval(|_| 1 << 30), None);
    }

    #[test]
    fn reads_only_what_the_run_hasnt_written() {
        // `(i % 7) - 3` into slot 9: slot 9 holds anything before the run.
        let ops = vec![IntOp { op: Arith::Mod, lhs: Slot(8), rhs: K(7), dest: 9 }, IntOp { op: Arith::Sub, lhs: Slot(9), rhs: K(3), dest: 9 }];
        assert_eq!(Fused::new(ops).eval(|s| if s == 8 { 15 } else { panic!("read slot {s}") }), Some(vec![(9, -2)]));
    }

    #[test]
    fn never_past_exact() {
        let mul = IntOp { op: Arith::Mul, lhs: Slot(1), rhs: K(1 << 20), dest: 1 };
        assert!(exact(&[mul]));
        assert!(!exact(&[mul, mul]));
        assert!(!exact(&[IntOp { op: Arith::Mul, lhs: Slot(1), rhs: K(-2), dest: 1 }]));
        assert!(!exact(&[IntOp { op: Arith::Mod, lhs: Slot(1), rhs: Slot(2), dest: 1 }]));
        let add = IntOp { op: Arith::Add, lhs: Slot(1), rhs: K(1), dest: 1 };
        assert!(exact(&[add; MAX_RUN]));
        assert!(!exact(&[add; MAX_RUN + 1]));
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
    fn agrees_with_lua_numbers() {
        // Random exact runs on edge and random integers, against Lua's doubles: what a fused
        // operation writes, it writes as Lua computes it, and it writes nothing only where a slot
        // it would write doesn't fit.
        let mut seed = 0x9e3779b97f4a7c15u64;
        let mut rand = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let edges = [0, 1, -1, 2, 255, 256, -256, i32::MAX, i32::MIN, i32::MAX - 1, i32::MIN + 1, 1 << 30, -(1 << 30), 65535];
        let (mut fit, mut left) = (0, 0);
        for _ in 0..200_000 {
            let mut operand = |rand: &mut dyn FnMut() -> u64| if rand() % 3 == 0 {
                K(match rand() % 4 { 0 => edges[(rand() % edges.len() as u64) as usize], 1 => 1 << (rand() % 20), _ => (rand() % 600) as i32 - 300 })
            } else {
                Slot((rand() % 4) as usize)
            };
            let ops: Vec<IntOp> = (0..(2 + rand() % 5)).map(|_| {
                let op = [Arith::Add, Arith::Sub, Arith::Mul, Arith::Mod][(rand() % 4) as usize];
                let (lhs, rhs) = (operand(&mut rand), operand(&mut rand));
                IntOp { op, lhs, rhs, dest: (rand() % 4) as usize }
            }).collect();
            if !exact(&ops) {
                continue;
            }
            let inputs: Vec<i32> = (0..4).map(|_| match rand() % 3 {
                0 => edges[(rand() % edges.len() as u64) as usize],
                _ => (rand() % 2000) as i32 - 1000,
            }).collect();
            let mut expected: Vec<f64> = inputs.iter().map(|&v| v as f64).collect();
            for op in &ops {
                expected[op.dest] = lua(op, &expected);
            }
            let fused = Fused::new(ops.clone());
            match fused.eval(|s| inputs[s]) {
                Some(writes) => {
                    fit += 1;
                    for (slot, v) in writes {
                        assert_eq!((v as f64).to_bits(), expected[slot].to_bits(), "{ops:?} on {inputs:?}");
                    }
                },
                None => {
                    left += 1;
                    assert!(fused.writes.iter().any(|&s| in_encoding(expected[s]).is_none()), "{ops:?} left on {inputs:?}");
                },
            }
        }
        assert!(fit > 1000 && left > 100, "fit {fit}, left {left}");
    }
}
