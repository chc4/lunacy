//! Fusing runs of integer arithmetic into one operation. See Note [Peephole fusion].

// Note [Peephole fusion]
// ~~~~~~~~~~~~~~~~~~~~~~
// Each integer operation in the integer encoding checks its own result fits, and boxes it, though
// the next operation often only reads it to compute another: `(p - 1) % 256 + 1` checks and boxes
// three times. A run of integer operations each reading the one before it can instead be one
// operation, computing in 64 bits and checking once. A run is fused as a pattern, a sequence of
// operations' shapes, each its own operation: the longest pattern matching where a run starts,
// then again after it.
//
// The fused operation computes every result exactly: its operations neither make a -0 nor exceed
// 2^53 from integers, so 64-bit integers give what doubles would. It checks that each slot it
// writes, as the last of its operations to write the slot leaves it, fits the integer encoding,
// and only then writes them all: where one doesn't fit, it writes nothing, and the code leaves
// for the interpreter at the run's first operation, which computes it all again in doubles. A
// slot only an earlier operation of the run writes, written again later in it, is never seen,
// and needs no check. A run that left once isn't fused again where it starts.

/// An arithmetic operation of the integer encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Arith {
    Add,
    Sub,
    Mul,
    /// Floored, as Lua's `%`.
    Mod,
    /// Floored: `math.floor(a / b)`, as of an integer's quotient. See Note [Quotients] in `specialize`.
    FloorDiv,
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

/// What a pattern matches an operation by: its operation, its operands' kinds, and whether a
/// constant divisor is a power of two (a mask, or a shift).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Shape {
    /// `r + k`, or `k + r`.
    AddK,
    /// `r - k`.
    SubK,
    /// `k - r`.
    KSub,
    /// `r * k`, or `k * r`, `k` positive.
    MulK,
    /// `r % k`, `k` a positive power of two.
    MaskK,
    /// `r % k`, `k` positive and not a power of two.
    ModK,
    /// `floor(r / k)`, `k` a positive power of two.
    ShiftK,
    /// `floor(r / k)`, `k` positive and not a power of two.
    FloorDivK,
    AddRR,
    SubRR,
}

impl IntOp {
    /// The operation's shape, if it can be fused: never one that could make a -0 (a product with
    /// a factor that isn't a positive constant) or divide by a slot.
    pub fn shape(&self) -> Option<Shape> {
        use Operand::{K, Slot};
        let pow2 = |k: i32| k > 0 && k & (k - 1) == 0;
        Some(match (self.op, self.lhs, self.rhs) {
            (Arith::Add, Slot(_), K(_)) | (Arith::Add, K(_), Slot(_)) => Shape::AddK,
            (Arith::Sub, Slot(_), K(_)) => Shape::SubK,
            (Arith::Sub, K(_), Slot(_)) => Shape::KSub,
            (Arith::Mul, Slot(_), K(k)) | (Arith::Mul, K(k), Slot(_)) if k > 0 => Shape::MulK,
            (Arith::Mod, Slot(_), K(k)) if pow2(k) => Shape::MaskK,
            (Arith::Mod, Slot(_), K(k)) if k > 0 => Shape::ModK,
            (Arith::FloorDiv, Slot(_), K(k)) if pow2(k) => Shape::ShiftK,
            (Arith::FloorDiv, Slot(_), K(k)) if k > 0 => Shape::FloorDivK,
            (Arith::Add, Slot(_), Slot(_)) => Shape::AddRR,
            (Arith::Sub, Slot(_), Slot(_)) => Shape::SubRR,
            _ => return None,
        })
    }

    fn reads(&self, slot: usize) -> bool {
        self.lhs == Operand::Slot(slot) || self.rhs == Operand::Slot(slot)
    }

    /// The operation of `l` and `r`, exactly.
    fn apply(&self, l: i64, r: i64) -> i64 {
        match self.op {
            Arith::Add => l + r,
            Arith::Sub => l - r,
            Arith::Mul => l * r,
            Arith::Mod => l.rem_euclid(r),
            Arith::FloorDiv => l.div_euclid(r),
        }
    }

    /// The most the result's magnitude can be, given each operand's: at most 2^31 for a slot.
    fn bound(&self, l: u128, r: u128) -> u128 {
        match self.op {
            Arith::Add | Arith::Sub => l + r,
            Arith::Mul => l * r,
            // Of a positive constant divisor.
            Arith::Mod => r,
            Arith::FloorDiv => l / r.max(1) + 1,
        }
    }
}

/// A run of operations fused into one.
pub struct Pattern {
    pub name: &'static str,
    pub shapes: &'static [Shape],
}

/// One of the input's items: an integer operation, or anything else, which no run spans.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Item {
    Int(IntOp),
    Other,
}

/// What the items become, in order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Emit {
    /// The input's item at this index, as it was.
    Item(usize),
    Fused(Fused),
}

/// A run of the input's integer operations, one operation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fused {
    /// The index of the run's first item, where the code leaves for the interpreter when a
    /// result doesn't fit.
    pub start: usize,
    /// Which of the patterns it is.
    pub pattern: usize,
    pub ops: Vec<IntOp>,
    /// The slots it writes, in the order the run first writes them.
    pub writes: Vec<usize>,
}

impl Fused {
    /// Each slot it writes and the value it leaves there, from the slots' values before the run,
    /// as `read` gives them; or none, where one doesn't fit the integer encoding.
    pub fn eval(&self, read: impl Fn(usize) -> i32) -> Option<Vec<(usize, i32)>> {
        let mut written: Vec<(usize, i64)> = Vec::new();
        let value = |written: &Vec<(usize, i64)>, operand: Operand| match operand {
            Operand::K(k) => k as i64,
            Operand::Slot(s) => written.iter().rev().find(|(w, _)| *w == s).map_or(read(s) as i64, |(_, v)| *v),
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
}

/// The items, with each run of integer operations a pattern matches fused: the longest matching
/// where a run starts, unless `failed` says a run fused from there left before. See Note
/// [Peephole fusion].
pub fn fuse(items: &[Item], patterns: &[Pattern], failed: impl Fn(usize) -> bool) -> Vec<Emit> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < items.len() {
        let best = if failed(i) { None } else {
            patterns.iter().enumerate()
                .filter(|(_, p)| p.shapes.len() >= 2 && matches(&items[i..], p.shapes))
                .max_by_key(|(_, p)| p.shapes.len())
        };
        match best {
            Some((pattern, p)) => {
                let ops: Vec<IntOp> = items[i..i + p.shapes.len()].iter().map(|item| match item {
                    Item::Int(op) => *op,
                    Item::Other => unreachable!(),
                }).collect();
                let mut writes = Vec::new();
                for op in &ops {
                    if !writes.contains(&op.dest) {
                        writes.push(op.dest);
                    }
                }
                out.push(Emit::Fused(Fused { start: i, pattern, ops, writes }));
                i += p.shapes.len();
            }
            None => {
                out.push(Emit::Item(i));
                i += 1;
            }
        }
    }
    out
}

/// Whether the items start with a run of `shapes`: integer operations of those shapes, each
/// after the first reading the one before it, whose results are exact. See Note [Peephole fusion].
fn matches(items: &[Item], shapes: &[Shape]) -> bool {
    if items.len() < shapes.len() {
        return false;
    }
    // The most each slot's magnitude can be, as the run has written it so far.
    let mut bounds: Vec<(usize, u128)> = Vec::new();
    let bound = |bounds: &Vec<(usize, u128)>, operand: Operand| match operand {
        Operand::K(k) => (k as i64).unsigned_abs() as u128,
        Operand::Slot(s) => bounds.iter().rev().find(|(w, _)| *w == s).map_or(1 << 31, |(_, b)| *b),
    };
    let mut prev: Option<IntOp> = None;
    for (item, shape) in items.iter().zip(shapes) {
        let Item::Int(op) = item else { return false };
        if op.shape() != Some(*shape) {
            return false;
        }
        if prev.is_some_and(|prev| !op.reads(prev.dest)) {
            return false;
        }
        let b = op.bound(bound(&bounds, op.lhs), bound(&bounds, op.rhs));
        if b > 1 << 53 {
            return false;
        }
        bounds.push((op.dest, b));
        prev = Some(*op);
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use Operand::{K, Slot};

    fn int(op: Arith, lhs: Operand, rhs: Operand, dest: usize) -> Item {
        Item::Int(IntOp { op, lhs, rhs, dest })
    }

    const INDEX: Pattern = Pattern { name: "SubMaskAdd", shapes: &[Shape::SubK, Shape::MaskK, Shape::AddK] };
    const MASK_ADD: Pattern = Pattern { name: "MaskAdd", shapes: &[Shape::MaskK, Shape::AddK] };
    const MUL_ADD: Pattern = Pattern { name: "MulAdd", shapes: &[Shape::MulK, Shape::AddRR] };

    #[test]
    fn fuses_an_index_computation() {
        // (p - 1) % 256 + 1, in place, as uxn.lua computes a stack index.
        let items = [int(Arith::Sub, Slot(6), K(1), 6), int(Arith::Mod, Slot(6), K(256), 6), int(Arith::Add, Slot(6), K(1), 6)];
        let out = fuse(&items, &[INDEX, MASK_ADD], |_| false);
        let [Emit::Fused(f)] = &out[..] else { panic!("{out:?}") };
        assert_eq!((f.start, f.pattern, f.writes.clone()), (0, 0, vec![6]));
        assert_eq!(f.eval(|_| 0), Some(vec![(6, 256)]));
        assert_eq!(f.eval(|_| 257), Some(vec![(6, 1)]));
    }

    #[test]
    fn takes_the_longest_pattern_then_matches_again() {
        let items = [
            int(Arith::Sub, Slot(6), K(1), 6), int(Arith::Mod, Slot(6), K(256), 6), int(Arith::Add, Slot(6), K(1), 6),
            int(Arith::Mod, Slot(6), K(16), 7), int(Arith::Add, Slot(7), K(2), 7),
        ];
        let out = fuse(&items, &[MASK_ADD, INDEX], |_| false);
        assert!(matches!(&out[..], [Emit::Fused(a), Emit::Fused(b)] if a.pattern == 1 && b.pattern == 0 && b.start == 3), "{out:?}");
    }

    #[test]
    fn a_run_reads_the_operation_before_it() {
        // The add reads slot 3, not the mask's result.
        let items = [int(Arith::Mod, Slot(6), K(256), 6), int(Arith::Add, Slot(3), K(1), 7)];
        assert_eq!(fuse(&items, &[MASK_ADD], |_| false), vec![Emit::Item(0), Emit::Item(1)]);
    }

    #[test]
    fn other_items_end_a_run() {
        let items = [int(Arith::Mod, Slot(6), K(256), 6), Item::Other, int(Arith::Add, Slot(6), K(1), 6)];
        assert_eq!(fuse(&items, &[MASK_ADD], |_| false), vec![Emit::Item(0), Emit::Item(1), Emit::Item(2)]);
    }

    #[test]
    fn a_run_that_left_isnt_fused_again() {
        let items = [int(Arith::Mod, Slot(6), K(256), 6), int(Arith::Add, Slot(6), K(1), 6)];
        assert_eq!(fuse(&items, &[MASK_ADD], |start| start == 0), vec![Emit::Item(0), Emit::Item(1)]);
    }

    #[test]
    fn never_fuses_what_could_make_a_negative_zero() {
        for item in [int(Arith::Mul, Slot(1), K(-2), 1), int(Arith::Mul, Slot(1), K(0), 1), int(Arith::Mul, Slot(1), Slot(2), 1), int(Arith::Mod, Slot(1), Slot(2), 1)] {
            let Item::Int(op) = item else { unreachable!() };
            assert_eq!(op.shape(), None, "{op:?}");
        }
    }

    #[test]
    fn never_fuses_past_exact() {
        // 2^31 * 2^20 * 2^20 exceeds 2^53.
        const MULS: Pattern = Pattern { name: "MulMul", shapes: &[Shape::MulK, Shape::MulK] };
        let items = [int(Arith::Mul, Slot(1), K(1 << 20), 1), int(Arith::Mul, Slot(1), K(1 << 20), 1)];
        assert_eq!(fuse(&items, &[MULS], |_| false), vec![Emit::Item(0), Emit::Item(1)]);
    }

    #[test]
    fn checks_only_what_the_run_leaves() {
        // 2^30 + 2^30 doesn't fit, but the run overwrites it before anything sees it.
        let items = [int(Arith::Add, Slot(0), Slot(0), 1), int(Arith::Sub, Slot(1), Slot(0), 1)];
        let f = match &fuse(&items, &[Pattern { name: "AddSub", shapes: &[Shape::AddRR, Shape::SubRR] }], |_| false)[..] {
            [Emit::Fused(f)] => f.clone(),
            out => panic!("{out:?}"),
        };
        assert_eq!(f.eval(|_| 1 << 30), Some(vec![(1, 1 << 30)]));
        // Where it is left, it is checked.
        assert_eq!(Fused { writes: vec![1], ops: f.ops[..1].to_vec(), ..f.clone() }.eval(|_| 1 << 30), None);
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
            Arith::FloorDiv => (l / r).floor(),
        }
    }

    /// Whether a double is a value of the integer encoding: whole, in range, and not -0.
    fn integer(v: f64) -> Option<i32> {
        (v.fract() == 0.0 && v >= i32::MIN as f64 && v <= i32::MAX as f64 && v.to_bits() != (-0.0f64).to_bits()).then_some(v as i32)
    }

    #[test]
    fn agrees_with_lua_numbers() {
        // Random runs of random operations, on edge and random values, against Lua's doubles: what
        // a fused operation writes, it writes as Lua computes it, and it leaves only where a slot
        // it would write doesn't fit.
        let patterns = [
            INDEX, MASK_ADD, MUL_ADD,
            Pattern { name: "AddAdd", shapes: &[Shape::AddRR, Shape::AddK] },
            Pattern { name: "SubSub", shapes: &[Shape::KSub, Shape::SubRR, Shape::SubK] },
            Pattern { name: "ModFloor", shapes: &[Shape::ModK, Shape::FloorDivK, Shape::AddK] },
            Pattern { name: "ShiftMul", shapes: &[Shape::ShiftK, Shape::MulK, Shape::AddRR, Shape::MaskK] },
        ];
        let mut seed = 0x9e3779b97f4a7c15u64;
        let mut rand = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let edges = [0, 1, -1, 2, 255, 256, -256, i32::MAX, i32::MIN, i32::MAX - 1, i32::MIN + 1, 1 << 30, -(1 << 30), 65535];
        let (mut fused, mut left) = (0, 0);
        for _ in 0..200_000 {
            let mut operand = |rand: &mut dyn FnMut() -> u64| if rand() % 3 == 0 {
                K(match rand() % 4 { 0 => edges[(rand() % edges.len() as u64) as usize], 1 => 1 << (rand() % 20), _ => (rand() % 600) as i32 - 300 })
            } else {
                Slot((rand() % 4) as usize)
            };
            let items: Vec<Item> = (0..(2 + rand() % 5)).map(|_| {
                let op = [Arith::Add, Arith::Sub, Arith::Mul, Arith::Mod, Arith::FloorDiv][(rand() % 5) as usize];
                let (lhs, rhs) = (operand(&mut rand), operand(&mut rand));
                int(op, lhs, rhs, (rand() % 4) as usize)
            }).collect();
            let mut slots: Vec<f64> = (0..4).map(|_| match rand() % 3 {
                0 => edges[(rand() % edges.len() as u64) as usize] as f64,
                _ => ((rand() % 2000) as i64 - 1000) as f64,
            }).collect();
            let mut expected = slots.clone();
            for item in &items {
                let Item::Int(op) = item else { unreachable!() };
                expected[op.dest] = lua(op, &expected);
            }
            for emit in fuse(&items, &patterns, |_| false) {
                match emit {
                    Emit::Item(i) => {
                        let Item::Int(op) = &items[i] else { unreachable!() };
                        slots[op.dest] = lua(op, &slots);
                    }
                    Emit::Fused(f) => {
                        let before = slots.clone();
                        let mut interpreted = slots.clone();
                        for op in &f.ops {
                            interpreted[op.dest] = lua(op, &interpreted);
                        }
                        let inputs: Option<Vec<i32>> = before.iter().map(|&v| integer(v)).collect();
                        match inputs.and_then(|inputs| f.eval(|s| inputs[s])) {
                            Some(writes) => {
                                fused += 1;
                                for (slot, v) in writes {
                                    assert_eq!((v as f64).to_bits(), interpreted[slot].to_bits(), "{f:?} on {before:?}");
                                    slots[slot] = v as f64;
                                }
                            }
                            None => {
                                // It leaves only where its inputs aren't integers, or a slot it
                                // writes, as the interpreter computes it, doesn't fit.
                                left += 1;
                                assert!(before.iter().any(|&v| integer(v).is_none()) || f.writes.iter().any(|&s| integer(interpreted[s]).is_none()), "{f:?} left on {before:?}");
                                slots = interpreted;
                            }
                        }
                    }
                }
            }
            for (a, b) in slots.iter().zip(&expected) {
                assert!(a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan()), "{items:?}: {slots:?} vs {expected:?}");
            }
        }
        assert!(fused > 1000 && left > 100, "fused {fused}, left {left}");
    }
}
