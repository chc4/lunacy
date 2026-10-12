//! Fusing integer arithmetic into window ops, per value. See Note [Peephole fusion].

use std::rc::Rc;
use std::sync::LazyLock;

use crate::lboxed::LBoxed;
use crate::vm::{LValue, Opcode};
#[cfg(feature = "unreachable")]
use crate::unreachable;
use crate::window::{windowed, Window};

// Note [Peephole memory]
// ~~~~~~~~~~~~~~~~~~~~~~
// The peephole holds stores into tables' array parts as it holds integer values, as witchcraft does,
// but only those that leave the part's length and kind as they were, so nothing about the table but
// the element changes while one is held.
//
// An element is named by what the context knows of its table and key, the way witchcraft names
// memory by its space: two are one element where both are known equal, are different where their
// keys are different constants, and may be one otherwise. A store makes a held store into its
// element dead and depends on held stores into elements that may be its; a load of an element only
// one held store may be into is that store's value. A held store's registers are pinned as a spell's
// inputs are, so what names its element stays true while it is held.

// Note [Peephole fusion]
// ~~~~~~~~~~~~~~~~~~~~~~
// Each integer op checks that its result fits and boxes it, though the next often only reads it to
// compute another. The peephole holds them as witchcraft holds ops: one spell per slot, its value a
// computation of values from before anything held, so a chain is one op that checks once and a
// value overwritten unread is never computed. It is the coroutine the generators run in, so what it
// holds is suspended with it wherever compiling is, and code compiled from a point where it holds
// something is that point's own, never a version's. An inlined call's frame is held as well, made
// only once code inside it is laid out, so a callee whose code all folds returns into its caller's
// code having made no frame.
//
// What can't be held lays out only what it depends on, by witchcraft's two invariants: what it
// reads, and, first, what reads a register it writes as that register was. The rest stays held,
// unless what follows may observe it unwritten, by running again from before it or leaving for code
// that doesn't know it.
//
// A laid-out spell may fail. Its exit writes everything unwritten as Lua would and goes on from the
// instruction that laid it out, which runs again, so that instruction's own ops fail last.
//
// Every constant the context knows is folded, but what it folds to is known past it only if no load
// made the constant: a loaded constant's fact is contraction's to drop, and knowing what a loop's
// counter folds to would make a version of the loop per value.

/// An arithmetic operation of the integer encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Arith {
    Add,
    Sub,
    Mul,
    /// Floored, as Lua's `%`.
    Mod,
    /// Lua's `/`, a double.
    Div,
    /// `math.floor` of its left operand.
    Floor,
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
            Opcode::DIV => Arith::Div,
            _ => return None,
        };
        Some(IntOp { op, lhs, rhs, dest })
    }

    /// Loading constant `value` into `dest`: what it folds to, as the sum of it and nothing.
    pub fn constant(value: i32, dest: usize) -> Self {
        IntOp { op: Arith::Add, lhs: Operand::K(value), rhs: Operand::K(0), dest }
    }

    /// Its slot operands.
    pub fn reads(&self) -> impl Iterator<Item = usize> {
        [self.lhs, self.rhs].into_iter().filter_map(|o| match o { Operand::Slot(s) => Some(s), Operand::K(_) => None })
    }

    /// Its symbol, the register it steps, and its constant, if it is a step of a register by a
    /// constant: making no -0, a remainder a mask.
    fn step(&self) -> Option<(Sym, usize, i32)> {
        let (slot, k) = match (self.op, self.lhs, self.rhs) {
            (_, Operand::Slot(s), Operand::K(k)) => (s, k),
            (Arith::Add | Arith::Mul, Operand::K(k), Operand::Slot(s)) => (s, k),
            _ => return None,
        };
        match self.op {
            Arith::Add => Some((Sym::K(ADD), slot, k)),
            Arith::Sub => Some((Sym::K(SUB), slot, k)),
            Arith::Mul if k > 0 => Some((Sym::K(MUL), slot, k)),
            Arith::Mod if k > 0 && k & (k - 1) == 0 => Some((Sym::K(MASK), slot, k - 1)),
            Arith::Div if k > 0 => Some((Sym::K(DIV), slot, k)),
            Arith::Floor => Some((Sym::K(FLOOR), slot, 0)),
            _ => None,
        }
    }

    /// Its symbol and registers, if it is a sum or difference of two registers.
    fn pair(&self) -> Option<(Sym, usize, usize)> {
        match (self.op, self.lhs, self.rhs) {
            (Arith::Add, Operand::Slot(l), Operand::Slot(r)) => Some((Sym::RR(ADD), l, r)),
            (Arith::Sub, Operand::Slot(l), Operand::Slot(r)) => Some((Sym::RR(SUB), l, r)),
            _ => None,
        }
    }
}

/// An element of a table's array part: the table's register, and the key, a register or a
/// constant. See Note [Peephole memory].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Element {
    pub table: usize,
    pub key: Operand,
}

/// Whether two cells are the same, can't be, or may be. See Note [Peephole memory].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Alias {
    Same,
    Disjoint,
    May,
}

/// What a store stores: a register's value, or a constant's, boxed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Stored {
    Slot(usize),
    Boxed(u64),
}

/// A load or store of an element already in its table's array part, which leaves the array part's
/// length and kind as they are: a store of a value that isn't nil and widens no kind. See Note
/// [Peephole memory].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MemOp {
    Load { cell: Element, dest: usize },
    Store { cell: Element, value: Stored },
}

/// A store held, unwritten: of `value` into `cell`, as `window` stores it, in instruction `at`,
/// after the held stores `after` whose cells may be its own.
#[derive(Clone, Debug)]
pub struct Store {
    id: usize,
    pub cell: Element,
    pub value: Stored,
    pub window: Rc<dyn Window>,
    pub at: usize,
    after: Vec<usize>,
}

impl Store {
    /// The registers it reads, as they were before any held operation.
    fn inputs(&self) -> impl Iterator<Item = usize> + '_ {
        let key = match self.cell.key { Operand::Slot(slot) => Some(slot), Operand::K(_) => None };
        let value = match self.value { Stored::Slot(slot) => Some(slot), Stored::Boxed(_) => None };
        std::iter::once(self.cell.table).chain(key).chain(value)
    }
}

/// What an op the peephole doesn't hold needs of what it holds: the registers it reads and those
/// it writes, and whether it may read or write memory. See Note [Peephole fusion].
#[derive(Clone, Debug, Default)]
pub struct Need {
    pub reads: Vec<usize>,
    pub writes: Vec<usize>,
    pub memory: bool,
}

/// What a load of a cell becomes: the value a held store stores there, or itself, after the held
/// stores whose cells may be its, laid out.
pub enum Load {
    Forward(Stored),
    After(Vec<Rc<dyn Window>>),
}

/// Whether integer operations are held to fuse (Note [Peephole fusion]); set `LUNACY_NO_FUSION`
/// for none, to compare.
pub fn fuses() -> bool {
    static FUSES: LazyLock<bool> = LazyLock::new(|| std::env::var_os("LUNACY_NO_FUSION").is_none());
    *FUSES
}

// Steps of a register by a constant, and sums and differences of two.
const ADD: u8 = 0;
const SUB: u8 = 1;
const MUL: u8 = 2;
/// `k` the mask.
const MASK: u8 = 3;
/// A quotient by a positive constant, and its floor. See Note [Peephole fusion].
const DIV: u8 = 4;
const FLOOR: u8 = 5;
// Guards on a key: `InArray`'s, and `InArrayHeld`'s.
const IN_ARRAY: u8 = 0;
const HELD: u8 = 1;

/// What a rule matches an item of a spell by.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Sym {
    /// A step of the value by a constant.
    K(u8),
    /// A sum or difference of the value and another register; first, of two registers.
    RR(u8),
    /// A guard on the value as a key.
    Guard(u8),
    /// A constant: what an operation of constants folds to.
    Const,
}

/// Step `S` of `x` by `k`: its result, if it fits.
fn step<const S: u8>(x: i32, k: i32) -> Option<i32> {
    match S {
        ADD => x.checked_add(k),
        SUB => x.checked_sub(k),
        MUL => x.checked_mul(k),
        MASK => Some(x & k),
        _ => unreachable!(),
    }
}

/// Step `S` of `x` by `k`, where it fits.
fn wrapping<const S: u8>(x: i32, k: i32) -> i32 {
    match S {
        ADD => x.wrapping_add(k),
        SUB => x.wrapping_sub(k),
        MUL => x.wrapping_mul(k),
        MASK => x & k,
        _ => unreachable!(),
    }
}

/// `x` and `y`'s sum or difference, `O`, if it fits.
fn pair<const O: u8>(x: i32, y: i32) -> Option<i32> {
    match O {
        ADD => x.checked_add(y),
        SUB => x.checked_sub(y),
        _ => unreachable!(),
    }
}

/// `x` and `y`'s sum or difference, `O`, where it fits.
fn wrapping_pair<const O: u8>(x: i32, y: i32) -> i32 {
    match O {
        ADD => x.wrapping_add(y),
        SUB => x.wrapping_sub(y),
        _ => unreachable!(),
    }
}

/// Step `S` of `x` by `k`, as Lua computes it, in doubles.
fn lua_step<const S: u8>(x: f64, k: i32) -> f64 {
    let k = k as f64;
    match S {
        ADD => x + k,
        SUB => x - k,
        MUL => x * k,
        MASK => x - (x / (k + 1.0)).floor() * (k + 1.0),
        _ => unreachable!(),
    }
}

/// `x` and `y`'s sum or difference, `O`, as Lua computes it.
fn lua_pair<const O: u8>(x: f64, y: f64) -> f64 {
    match O {
        ADD => x + y,
        SUB => x - y,
        _ => unreachable!(),
    }
}

/// `op` of constants `l` and `r` as Lua computes it, if that is a value of the integer encoding:
/// whole, in range, and not -0.
fn fold(op: Arith, l: i32, r: i32) -> Option<i32> {
    let (l, r) = (l as f64, r as f64);
    let v = match op {
        Arith::Add => l + r,
        Arith::Sub => l - r,
        Arith::Mul => l * r,
        Arith::Mod => l - (l / r).floor() * r,
        // A quotient is a double, though whole: its slot is typed so.
        Arith::Div => return None,
        Arith::Floor => l.floor(),
    };
    (v.fract() == 0.0 && v >= i32::MIN as f64 && v <= i32::MAX as f64 && v.to_bits() != (-0.0f64).to_bits()).then_some(v as i32)
}

/// Whether integer `key` passes guard `G` of `table`.
fn passes<const G: u8>(owner: &crate::Owner, table: LBoxed, key: i32) -> bool {
    let LValue::Table(tab) = table.unbox() else { unreachable!() };
    let array = &tab.ro(owner).array;
    let slot = crate::generators::integer_slot(key);
    match G {
        IN_ARRAY => slot < array.len(),
        HELD => array.get(slot).is_some_and(|v| !v.is_nil()),
        _ => unreachable!(),
    }
}

/// What a spell's ops take: its constants, in order, and its registers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Matched {
    pub ks: Vec<i32>,
    pub lhs: usize,
    pub rhs: Option<usize>,
    pub table: Option<usize>,
    pub dest: usize,
}

/// A spell's ops, as its rule makes them.
pub struct Ops {
    /// Its chain, computed and written where every step fits and the guard it ends in passes,
    /// else its cold path, writing nothing it would need: a slot it writes that it reads too
    /// keeps its value.
    pub fused: Rc<dyn Window>,
    /// Its chain, computed and written, where it fits.
    pub compute: Rc<dyn Window>,
    /// Its chain's value as Lua computes it, written, any guard it ends in left out.
    pub materialize: Rc<dyn Window>,
}

/// A rule: the chain it matches, and its ops.
pub struct Rule {
    pub name: &'static str,
    pub pattern: &'static [Sym],
    pub make: fn(&Matched) -> Ops,
}

/// The constants of `$m` as holes, for each `$k`.
macro_rules! holes {
    ($m:ident;) => { [0u64; 0] };
    ($m:ident; $($k:ident)*) => {{
        let mut ks = $m.ks.iter();
        [$({ let _ = stringify!($k); (*ks.next().unwrap()) as u32 as u64 }),*]
    }};
}

/// A rule `$rule` and its ops `$fused`, `$compute` and `$materialize`, over a chain of steps of a
/// register by constants `[S k, ..]`, ending in a guard `in G` or not; first a sum or difference
/// of two registers `rr O`; or one step then a sum or difference with another register. Its chain's
/// value is `$value`, from its operands, if every step fits, `$wrapped` where it does, `$lua` as
/// Lua computes it, from `$value_in`, and `$test` whether it passes any guard; its cold path writes
/// `$kept`, the operand its slot is, if any (`alias` saying which).
macro_rules! rule {
    (@ops [$($memory:ident)?] $m:ident, $alias:ident, $rule:ident, $fused:ident, $compute:ident, $materialize:ident, [$($sym:expr),+], ($($ks:ident),*),
        ($($input:ident),+), ($($slot:expr),+), ($($value_in:ident),+), ($($value_slot:expr),+),
        $value:expr, $wrapped:expr, $lua:expr, $test:expr, $kept:expr) => {
        windowed!($($memory)? $fused, [$($ks: u64,)* $alias: u64], [], |owner, state, base, tag| ($($input,)+ out dest) {
            match $value {
                Some(n) if ($test)(owner, n) => {
                    *dest = LBoxed::from_int_tagged(n, tag);
                    false
                },
                _ => {
                    core::intrinsics::cold_path();
                    true
                },
            }
        } cold {
            *dest = $kept;
            1
        });
        windowed!($compute, [$($ks: u64),*], [], |owner, state, base, tag| ($($input,)+ out dest) {
            *dest = LBoxed::from_int_tagged($wrapped, tag);
        });
        windowed!($materialize, [$($ks: u64),*], [], |owner, state, base| ($($value_in,)+ out dest) {
            *dest = LBoxed::from_number($lua);
        });
        const $rule: Rule = Rule { name: stringify!($rule), pattern: &[$($sym),+], make: |$m| {
            let [$($ks),*] = holes!($m; $($ks)*);
            let $alias = ($m.rhs == Some($m.dest)) as u64;
            let with = |slots: &[usize]| { let mut out = slots.to_vec(); out.push($m.dest); out };
            Ops {
                fused: Rc::new($fused::new($($ks,)* $alias, &with(&[$($slot),+]))),
                compute: Rc::new($compute::new($($ks,)* &with(&[$($slot),+]))),
                materialize: Rc::new($materialize::new($($ks,)* &with(&[$($value_slot),+]))),
            }
        }};
    };
    ($rule:ident, $fused:ident, $compute:ident, $materialize:ident = [$($s:ident $k:ident),+]) => {
        rule!(@ops [] m, alias, $rule, $fused, $compute, $materialize, [$(Sym::K($s)),+], ($($k),+), (lhs), (m.lhs), (lhs), (m.lhs),
            (|| -> Option<i32> { let x = lhs.as_int(); $(let x = step::<$s>(x, $k as i32)?;)+ Some(x) })(),
            { let x = lhs.as_int(); $(let x = wrapping::<$s>(x, $k as i32);)+ x },
            { let x = lhs.as_int() as f64; $(let x = lua_step::<$s>(x, $k as i32);)+ x },
            |_, _| true, { let _ = alias; lhs });
    };
    ($rule:ident, $fused:ident, $compute:ident, $materialize:ident = [$($s:ident $k:ident),+] in $g:ident) => {
        rule!(@ops [properties] m, alias, $rule, $fused, $compute, $materialize, [$(Sym::K($s),)+ Sym::Guard($g)], ($($k),+), (table, lhs), (m.table.unwrap(), m.lhs), (lhs), (m.lhs),
            (|| -> Option<i32> { let x = lhs.as_int(); $(let x = step::<$s>(x, $k as i32)?;)+ Some(x) })(),
            { let x = lhs.as_int(); $(let x = wrapping::<$s>(x, $k as i32);)+ x },
            { let x = lhs.as_int() as f64; $(let x = lua_step::<$s>(x, $k as i32);)+ x },
            |owner, x| passes::<$g>(owner, table, x), { let _ = (alias, table); lhs });
    };
    ($rule:ident, $fused:ident, $compute:ident, $materialize:ident = rr $o:ident [$($s:ident $k:ident),*]) => {
        rule!(@ops [] m, alias, $rule, $fused, $compute, $materialize, [Sym::RR($o) $(, Sym::K($s))*], ($($k),*), (lhs, rhs), (m.lhs, m.rhs.unwrap()), (lhs, rhs), (m.lhs, m.rhs.unwrap()),
            (|| -> Option<i32> { let x = pair::<$o>(lhs.as_int(), rhs.as_int())?; $(let x = step::<$s>(x, $k as i32)?;)* Some(x) })(),
            { let x = wrapping_pair::<$o>(lhs.as_int(), rhs.as_int()); $(let x = wrapping::<$s>(x, $k as i32);)* x },
            { let x = lua_pair::<$o>(lhs.as_int() as f64, rhs.as_int() as f64); $(let x = lua_step::<$s>(x, $k as i32);)* x },
            |_, _| true, if alias != 0 { rhs } else { lhs });
    };
    ($rule:ident, $fused:ident, $compute:ident, $materialize:ident = [$s:ident $k:ident] rr $o:ident) => {
        rule!(@ops [] m, alias, $rule, $fused, $compute, $materialize, [Sym::K($s), Sym::RR($o)], ($k), (lhs, rhs), (m.lhs, m.rhs.unwrap()), (lhs, rhs), (m.lhs, m.rhs.unwrap()),
            (|| -> Option<i32> { pair::<$o>(step::<$s>(lhs.as_int(), $k as i32)?, rhs.as_int()) })(),
            wrapping_pair::<$o>(wrapping::<$s>(lhs.as_int(), $k as i32), rhs.as_int()),
            lua_pair::<$o>(lua_step::<$s>(lhs.as_int() as f64, $k as i32), rhs.as_int() as f64),
            |_, _| true, if alias != 0 { rhs } else { lhs });
    };
}

// uxn.lua's: `s[p + 1]`, `(p - 1) % 256 + 1`, `(pc + 1) % 65536 + 1`, `t % 256 + 1`, `(t + 128) % 256 -
// 128`, `(t + 1) % 256`, `(p + k) % 256`, `(p + k + 1) % 256`, `(p + k - 1) % 256`, `n * 256 + t`,
// keys checked as reads (`InArrayHeld`) or writes (`InArray`), and every prefix.
rule!(ADD_, FusedAdd, ComputeAdd, MaterializeAdd = [ADD a]);
rule!(SUB_, FusedSub, ComputeSub, MaterializeSub = [SUB a]);
rule!(MUL_, FusedMul, ComputeMul, MaterializeMul = [MUL a]);
rule!(MASK_, FusedMask, ComputeMask, MaterializeMask = [MASK a]);
rule!(SUB_MASK, FusedSubMask, ComputeSubMask, MaterializeSubMask = [SUB a, MASK b]);
rule!(ADD_MASK, FusedAddMask, ComputeAddMask, MaterializeAddMask = [ADD a, MASK b]);
rule!(MASK_ADD, FusedMaskAdd, ComputeMaskAdd, MaterializeMaskAdd = [MASK a, ADD b]);
rule!(SUB_MASK_ADD, FusedSubMaskAdd, ComputeSubMaskAdd, MaterializeSubMaskAdd = [SUB a, MASK b, ADD c]);
rule!(ADD_MASK_ADD, FusedAddMaskAdd, ComputeAddMaskAdd, MaterializeAddMaskAdd = [ADD a, MASK b, ADD c]);
rule!(ADD_MASK_SUB, FusedAddMaskSub, ComputeAddMaskSub, MaterializeAddMaskSub = [ADD a, MASK b, SUB c]);
rule!(ADD_IN, FusedAddIn, ComputeAddIn, MaterializeAddIn = [ADD a] in IN_ARRAY);
rule!(ADD_HELD, FusedAddHeld, ComputeAddHeld, MaterializeAddHeld = [ADD a] in HELD);
rule!(MASK_ADD_IN, FusedMaskAddIn, ComputeMaskAddIn, MaterializeMaskAddIn = [MASK a, ADD b] in IN_ARRAY);
rule!(MASK_ADD_HELD, FusedMaskAddHeld, ComputeMaskAddHeld, MaterializeMaskAddHeld = [MASK a, ADD b] in HELD);
rule!(SUB_MASK_ADD_IN, FusedSubMaskAddIn, ComputeSubMaskAddIn, MaterializeSubMaskAddIn = [SUB a, MASK b, ADD c] in IN_ARRAY);
rule!(SUB_MASK_ADD_HELD, FusedSubMaskAddHeld, ComputeSubMaskAddHeld, MaterializeSubMaskAddHeld = [SUB a, MASK b, ADD c] in HELD);
rule!(ADD_MASK_ADD_IN, FusedAddMaskAddIn, ComputeAddMaskAddIn, MaterializeAddMaskAddIn = [ADD a, MASK b, ADD c] in IN_ARRAY);
rule!(ADD_MASK_ADD_HELD, FusedAddMaskAddHeld, ComputeAddMaskAddHeld, MaterializeAddMaskAddHeld = [ADD a, MASK b, ADD c] in HELD);
rule!(RR_ADD, FusedPairAdd, ComputePairAdd, MaterializePairAdd = rr ADD []);
rule!(RR_ADD_MASK, FusedPairAddMask, ComputePairAddMask, MaterializePairAddMask = rr ADD [MASK a]);
rule!(RR_ADD_ADD, FusedPairAddAdd, ComputePairAddAdd, MaterializePairAddAdd = rr ADD [ADD a]);
rule!(RR_ADD_ADD_MASK, FusedPairAddAddMask, ComputePairAddAddMask, MaterializePairAddAddMask = rr ADD [ADD a, MASK b]);
rule!(RR_ADD_SUB, FusedPairAddSub, ComputePairAddSub, MaterializePairAddSub = rr ADD [SUB a]);
rule!(RR_ADD_SUB_MASK, FusedPairAddSubMask, ComputePairAddSubMask, MaterializePairAddSubMask = rr ADD [SUB a, MASK b]);
rule!(MUL_RR_ADD, FusedMulPairAdd, ComputeMulPairAdd, MaterializeMulPairAdd = [MUL a] rr ADD);

// An integer's quotient by a positive constant `k`, a double as Lua's `/` makes; and its floor, an
// integer: the floored division, a shift for a power of two.
windowed!(ComputeDiv, [k: u64], [], |owner, state, base| (lhs, out dest) {
    *dest = LBoxed::from_double(lhs.as_int() as f64 / k as i32 as f64);
});
windowed!(ComputeDivFloor, [k: u64], [], |owner, state, base, tag| (lhs, out dest) {
    *dest = LBoxed::from_int_tagged(lhs.as_int().div_euclid(k as i32), tag);
});
windowed!(ComputeDivFloorShift, [shift: u64], [], |owner, state, base, tag| (lhs, out dest) {
    *dest = LBoxed::from_int_tagged(lhs.as_int() >> shift, tag);
});
const DIV_: Rule = Rule { name: "DIV_", pattern: &[Sym::K(DIV)], make: |m| {
    let op: Rc<dyn Window> = Rc::new(ComputeDiv::new(m.ks[0] as u32 as u64, &[m.lhs, m.dest]));
    Ops { fused: op.clone(), compute: op.clone(), materialize: op }
}};
const DIV_FLOOR: Rule = Rule { name: "DIV_FLOOR", pattern: &[Sym::K(DIV), Sym::K(FLOOR)], make: |m| {
    let k = m.ks[0];
    let op: Rc<dyn Window> = if k & (k - 1) == 0 {
        Rc::new(ComputeDivFloorShift::new(k.trailing_zeros() as u64, &[m.lhs, m.dest]))
    } else {
        Rc::new(ComputeDivFloor::new(k as u32 as u64, &[m.lhs, m.dest]))
    };
    Ops { fused: op.clone(), compute: op.clone(), materialize: op }
}};

// A constant, loaded.
const CONST_: Rule = Rule { name: "CONST_", pattern: &[Sym::Const], make: |m| {
    let load: Rc<dyn Window> = Rc::new(crate::generators::LoadK::new(LBoxed::from_int(m.ks[0]).bits(), &[m.dest]));
    Ops { fused: load.clone(), compute: load.clone(), materialize: load }
}};

/// Every rule.
pub static RULES: &[Rule] = &[
    CONST_, DIV_, DIV_FLOOR,
    ADD_, SUB_, MUL_, MASK_, SUB_MASK, ADD_MASK, MASK_ADD, SUB_MASK_ADD, ADD_MASK_ADD, ADD_MASK_SUB,
    ADD_IN, ADD_HELD, MASK_ADD_IN, MASK_ADD_HELD, SUB_MASK_ADD_IN, SUB_MASK_ADD_HELD, ADD_MASK_ADD_IN, ADD_MASK_ADD_HELD,
    RR_ADD, RR_ADD_MASK, RR_ADD_ADD, RR_ADD_ADD_MASK, RR_ADD_SUB, RR_ADD_SUB_MASK, MUL_RR_ADD,
];

/// The rules as a state machine: a trie of their patterns, each node the rule ending there.
struct Trie {
    next: Vec<Vec<(Sym, usize)>>,
    rule: Vec<Option<usize>>,
}

static TRIE: LazyLock<Trie> = LazyLock::new(|| {
    let mut trie = Trie { next: vec![Vec::new()], rule: vec![None] };
    for (i, rule) in RULES.iter().enumerate() {
        let mut node = 0;
        for &sym in rule.pattern {
            node = match trie.next[node].iter().find(|(s, _)| *s == sym) {
                Some(&(_, n)) => n,
                None => {
                    trie.next.push(Vec::new());
                    trie.rule.push(None);
                    let n = trie.next.len() - 1;
                    trie.next[node].push((sym, n));
                    n
                }
            };
        }
        assert!(trie.rule[node].is_none(), "two rules match {:?}", rule.pattern);
        trie.rule[node] = Some(i);
    }
    // Every prefix is a rule, so a spell always is one.
    assert!(trie.rule[1..].iter().all(Option::is_some), "a prefix of a rule isn't one");
    trie
});

impl Trie {
    fn step(&self, node: usize, sym: Sym) -> Option<usize> {
        self.next[node].iter().find(|(s, _)| *s == sym).map(|&(_, n)| n)
    }
}

/// The guard a spell can end in that `test` is, if it is one: its kind, and the slots of its table
/// and key.
pub fn guard(test: &dyn Window) -> Option<(u8, usize, usize)> {
    let kind = match test.name() {
        "InArray" => IN_ARRAY,
        "InArrayHeld" => HELD,
        _ => return None,
    };
    match test.operands() {
        &[table, key] if table != key => Some((kind, table, key)),
        _ => None,
    }
}

/// A suspended computation of slot `dest`. See Note [Peephole fusion].
#[derive(Clone, Debug)]
pub struct Spell {
    node: usize,
    pub dest: usize,
    /// The slots it reads, as they were before any held operation.
    pub inputs: Vec<usize>,
    matched: Matched,
    /// Ended in a guard.
    closed: bool,
    /// The instruction its last operation, or guard, is of.
    pub at: usize,
    /// What it was before that.
    before: Option<Box<Spell>>,
}

impl Spell {
    /// It, writing the slot `dest` names in place of its own, and reading those `input` does, as
    /// instruction `at`'s.
    fn renamed(&self, dest: &impl Fn(usize) -> usize, input: &impl Fn(usize) -> usize, at: usize) -> Spell {
        let mut spell = self.clone();
        spell.at = at;
        spell.dest = dest(self.dest);
        spell.inputs = self.inputs.iter().map(|&slot| input(slot)).collect();
        spell.matched = Matched {
            ks: self.matched.ks.clone(),
            lhs: input(self.matched.lhs),
            rhs: self.matched.rhs.map(input),
            table: self.matched.table.map(input),
            dest: dest(self.matched.dest),
        };
        spell.before = self.before.as_ref().map(|before| Box::new(before.renamed(dest, input, at)));
        spell
    }

    /// The spell of slot `dest` holding constant `value`, an operation of instruction `at` folded.
    fn constant(dest: usize, value: i32, at: usize) -> Spell {
        let node = TRIE.step(0, Sym::Const).expect("a constant is a rule");
        let matched = Matched { ks: vec![value], lhs: dest, rhs: None, table: None, dest };
        Spell { node, dest, inputs: Vec::new(), matched, closed: true, at, before: None }
    }

    /// The spell `op` begins, if a rule begins with it.
    fn start(op: &IntOp, at: usize) -> Option<Spell> {
        let (sym, matched, inputs) = if let Some((sym, slot, k)) = op.step() {
            (sym, Matched { ks: vec![k], lhs: slot, rhs: None, table: None, dest: op.dest }, vec![slot])
        } else {
            let (sym, l, r) = op.pair()?;
            (sym, Matched { ks: Vec::new(), lhs: l, rhs: Some(r), table: None, dest: op.dest }, vec![l, r])
        };
        let node = TRIE.step(0, sym)?;
        Some(Spell { node, dest: op.dest, inputs, matched, closed: false, at, before: None })
    }

    /// The spell of this spell's value then `op`, which reads it, into `op`'s slot, as a rule goes
    /// on: a step of the value by a constant, or a sum or difference of it and a register no spell
    /// writes, `held` saying which do.
    fn then(&self, op: &IntOp, held: impl Fn(usize) -> bool, at: usize) -> Option<Spell> {
        if self.closed {
            return None;
        }
        let mut spell = self.clone();
        spell.at = at;
        spell.before = Some(Box::new(self.clone()));
        if let Some((sym, slot, k)) = op.step() {
            spell.node = (slot == self.dest).then(|| TRIE.step(self.node, sym)).flatten()?;
            spell.matched.ks.push(k);
        } else {
            // The value first: a sum's operands either way round.
            let (sym, l, r) = op.pair()?;
            let other = match (l == self.dest, r == self.dest) {
                (true, false) => r,
                (false, true) if sym == Sym::RR(ADD) => l,
                _ => return None,
            };
            if held(other) || self.matched.rhs.is_some() {
                return None;
            }
            spell.node = TRIE.step(self.node, sym)?;
            spell.matched.rhs = Some(other);
            spell.inputs.push(other);
        }
        spell.dest = op.dest;
        spell.matched.dest = op.dest;
        Some(spell)
    }

    /// Whether guard `kind` of `table` on this spell's value joins it, ending it.
    fn join_guard(&mut self, kind: u8, table: usize, at: usize) -> bool {
        let Some(node) = (!self.closed && table != self.dest).then(|| TRIE.step(self.node, Sym::Guard(kind))).flatten() else { return false };
        self.before = Some(Box::new(self.clone()));
        self.at = at;
        self.node = node;
        self.matched.table = Some(table);
        self.inputs.push(table);
        self.closed = true;
        true
    }

    /// Its rule's ops.
    pub fn ops(&self) -> Ops {
        (RULES[TRIE.rule[self.node].expect("a spell is a rule")].make)(&self.matched)
    }

    /// Whether it can fail: a step but a mask's, or a guard. One that can't is only its
    /// computation: its check's test would fold away.
    pub fn can_fail(&self) -> bool {
        RULES[TRIE.rule[self.node].expect("a spell is a rule")].pattern.iter().any(|&sym| !matches!(sym, Sym::K(MASK | DIV | FLOOR) | Sym::Const))
    }

    /// Its rule's name.
    pub fn rule(&self) -> &'static str {
        RULES[TRIE.rule[self.node].expect("a spell is a rule")].name
    }

    /// Whether it is the same chain as `other`.
    fn same(&self, other: &Spell) -> bool {
        self.node == other.node && self.matched == other.matched && self.closed == other.closed
    }

    /// Whether it went on from `other`, so its check checks `other`'s.
    fn went_on_from(&self, other: &Spell) -> bool {
        std::iter::successors(self.before.as_deref(), |s| s.before.as_deref()).any(|s| s.same(other))
    }

    /// What it was before instruction `at`'s operations, if that wrote its slot.
    fn before_instruction(&self, at: usize) -> Option<&Spell> {
        let mut spell = self;
        while spell.at == at {
            spell = spell.before.as_deref()?;
        }
        (spell.dest == self.dest).then_some(spell)
    }
}

/// A spell laid out: its op, whether it can fail, and where it can, what its cold way writes:
/// the materializations of the spells not yet written, and the slots they leave unknown.
pub struct Laid {
    pub op: Rc<dyn Window>,
    pub checked: bool,
    pub exit: Vec<Rc<dyn Window>>,
    pub unknown: Vec<usize>,
}

/// What the peephole makes of an operation offered to it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Offer {
    /// It is held, in a spell.
    Held,
    /// It is held, its operands constants, as the constant it folds to.
    Folded(i32),
    /// Lay out every spell, then offer it again.
    Flush,
    /// It can't be held, with nothing held.
    Refused,
}

/// The spells the peephole holds, one per slot, and the stores. See Notes [Peephole fusion] and
/// [Peephole memory].
#[derive(Clone, Debug, Default)]
pub struct Spells {
    pub spells: Vec<Spell>,
    pub stores: Vec<Store>,
    /// The next store's id.
    next: usize,
}

impl Spells {
    /// Offer integer operation `op`: a spell of the value it reads and itself, or its own.
    pub fn offer(&mut self, op: &IntOp, at: usize, known: impl Fn(usize) -> Option<i32>) -> Offer {
        // A slot known to hold a constant is that constant.
        let constant = |o: Operand| match o {
            Operand::Slot(slot) => known(slot).map_or(o, Operand::K),
            k => k,
        };
        let op = &IntOp { lhs: constant(op.lhs), rhs: constant(op.rhs), ..*op };
        let holds = |slot: usize| self.spells.iter().any(|s| s.dest == slot);
        let read: Vec<usize> = op.reads().filter(|&slot| holds(slot)).collect();
        let folded = match (op.lhs, op.rhs) {
            (Operand::K(l), Operand::K(r)) => Some(fold(op.op, l, r)),
            _ => None,
        };
        let spell = match (folded, read.as_slice()) {
            (Some(value), _) => value.map(|value| Spell::constant(op.dest, value, at)),
            (None, []) => Spell::start(op, at),
            (None, [value]) => self.spells.iter().find(|s| s.dest == *value).unwrap().then(op, holds, at),
            _ => None,
        };
        let Some(spell) = spell else {
            // It is laid out as it is: what it overwrites unread isn't, and the rest first.
            if read.is_empty() {
                self.drop_overwritten(&[op.dest], &[]);
                if self.spells.is_empty() {
                    return Offer::Refused;
                }
            }
            return Offer::Flush;
        };
        // The value its slot held, unread but by it, overwritten.
        let mut next = self.clone();
        next.spells.retain(|s| s.dest != op.dest);
        next.spells.push(spell);
        if !next.last_can_fail() {
            return Offer::Flush;
        }
        *self = next;
        match folded {
            Some(Some(value)) => Offer::Folded(value),
            _ => Offer::Held,
        }
    }

    /// Whether the spell made last, with its instruction's operations, can be the last that can
    /// fail: every spell needed after it is one it went on from; and they are in an order.
    fn last_can_fail(&self) -> bool {
        let (last, others) = self.spells.split_last().unwrap();
        others.iter().all(|s| !last.inputs.contains(&s.dest) || last.went_on_from(s)) && self.order(last.at).is_some()
    }

    /// Offer the guard `test`, held as passed: joining the spell of the key it tests.
    pub fn offer_guard(&mut self, test: &dyn Window, at: usize) -> bool {
        let Some((kind, table, key)) = guard(test) else { return false };
        if self.spells.iter().any(|s| s.dest == table) {
            return false;
        }
        let mut next = self.clone();
        let Some(i) = next.spells.iter().position(|s| s.dest == key) else { return false };
        let mut spell = next.spells.remove(i);
        if !spell.join_guard(kind, table, at) {
            return false;
        }
        next.spells.push(spell);
        if !next.last_can_fail() {
            return false;
        }
        *self = next;
        true
    }

    /// Whether the guard `test` would join a spell.
    pub fn joins_guard(&self, test: &dyn Window, at: usize) -> bool {
        self.clone().offer_guard(test, at)
    }

    /// Whether they stay held across window op `window`: one with no way out, touching no memory,
    /// computing only from registers no spell writes into registers none reads, so an exit going on
    /// from before it runs it again to the same end. What it overwrites unread is then dropped.
    pub fn untouched(&self, window: &dyn Window) -> bool {
        window.memory() == crate::window::Memory::None && self.off_registers(window)
    }

    /// Whether window op `window` has no way out, reads no register a spell writes, and writes none
    /// a spell or store reads.
    pub fn off_registers(&self, window: &dyn Window) -> bool {
        !window.selects()
            && window.operands().iter().zip(window.accesses()).all(|(&slot, access)| match access {
                crate::window::Access::Read => self.spells.iter().all(|spell| spell.dest != slot),
                crate::window::Access::Write => self.inputs().all(|input| input != slot),
                crate::window::Access::Update => false,
            })
    }

    /// What it holds, the spells of slots `keeps` keeps writing the slots `dest` names, and
    /// everything reading the slots `input` does, as instruction `at`'s: a callee's, past its
    /// return into its caller's code. See Note [Peephole fusion].
    pub fn renamed(&self, dest: impl Fn(usize) -> usize, input: impl Fn(usize) -> usize, keeps: impl Fn(usize) -> bool, at: usize) -> Spells {
        let spells = self.spells.iter().filter(|spell| keeps(spell.dest)).map(|spell| spell.renamed(&dest, &input, at)).collect();
        let stores = self.stores.iter().map(|store| {
            let mut store = store.clone();
            let key = |key: Operand| match key { Operand::Slot(slot) => Operand::Slot(input(slot)), k => k };
            store.cell = Element { table: input(store.cell.table), key: key(store.cell.key) };
            if let Stored::Slot(slot) = store.value {
                store.value = Stored::Slot(input(slot));
            }
            let operands: Vec<usize> = store.window.operands().iter().map(|&slot| input(slot)).collect();
            store.window = store.window.with_operands(&operands);
            store.at = at;
            store
        }).collect();
        Spells { spells, stores, next: self.next }
    }

    /// Whether they stay held on both ways of guard `test` of instruction `at`, found out at
    /// runtime: one reading no register a spell writes, and no memory but an array part's length
    /// and kind, which no held store changes, unless one holds its instruction's operations, which
    /// a restart past it would repeat.
    pub fn across_guard(&self, test: &dyn Window, at: usize) -> bool {
        matches!(test.memory(), crate::window::Memory::None | crate::window::Memory::Properties)
            && self.spells.iter().all(|spell| !test.operands().contains(&spell.dest) && spell.at != at)
    }

    /// The registers the spells and stores read, as they were before any held operation.
    pub fn inputs(&self) -> impl Iterator<Item = usize> + '_ {
        self.spells.iter().flat_map(|spell| spell.inputs.iter().copied()).chain(self.stores.iter().flat_map(Store::inputs))
    }

    /// Hold the store of `value` into `cell`, as `window` stores it, in instruction `at`: a held
    /// store to the same cell is never read, and those to cells that may be its come before it.
    /// `alias` says how two cells are. How many held stores it made dead. See Note [Peephole
    /// memory].
    pub fn hold_store(&mut self, cell: Element, value: Stored, window: Rc<dyn Window>, at: usize, alias: impl Fn(Element, Element) -> Alias) -> usize {
        let dead = self.kill_stores(cell, &alias);
        let after = self.stores.iter().filter(|s| alias(s.cell, cell) == Alias::May).map(|s| s.id).collect();
        let id = self.next;
        self.next += 1;
        self.stores.push(Store { id, cell, value, window, at, after });
        dead
    }

    /// Drop the held stores into `cell`, which a store about to run into it makes dead: nothing
    /// reads the cell before it does. How many. See Note [Peephole memory].
    pub fn kill_stores(&mut self, cell: Element, alias: impl Fn(Element, Element) -> Alias) -> usize {
        let dead: Vec<usize> = self.stores.iter().filter(|s| alias(s.cell, cell) == Alias::Same).map(|s| s.id).collect();
        self.stores.retain(|s| !dead.contains(&s.id));
        for store in &mut self.stores {
            store.after.retain(|id| !dead.contains(id));
        }
        dead.len()
    }

    /// A load of `cell`: the value the one held store to it stores, if no other held store may be
    /// to it; else itself, after those that may be, and those before them, laid out. See Note
    /// [Peephole memory].
    pub fn load(&mut self, cell: Element, alias: impl Fn(Element, Element) -> Alias) -> Load {
        let to: Vec<(usize, Alias)> = self.stores.iter().map(|s| (s.id, alias(s.cell, cell))).filter(|(_, a)| *a != Alias::Disjoint).collect();
        if let [(id, Alias::Same)] = to.as_slice() {
            return Load::Forward(self.stores.iter().find(|s| s.id == *id).unwrap().value);
        }
        let mut laid: Vec<usize> = to.iter().map(|(id, _)| *id).collect();
        let mut i = 0;
        while i < laid.len() {
            let store = self.stores.iter().find(|s| s.id == laid[i]).unwrap();
            for &before in &store.after {
                if !laid.contains(&before) {
                    laid.push(before);
                }
            }
            i += 1;
        }
        // In the order they were held, which each's `after` keeps.
        let windows = self.stores.iter().filter(|s| laid.contains(&s.id)).map(|s| s.window.clone()).collect();
        self.stores.retain(|s| !laid.contains(&s.id));
        for store in &mut self.stores {
            store.after.retain(|id| !laid.contains(id));
        }
        Load::After(windows)
    }

    /// Drop the spells of slots `writes` that something about to be laid out writes, reading
    /// only `reads`: their values are never read.
    pub fn drop_overwritten(&mut self, writes: &[usize], reads: &[usize]) {
        self.spells.retain(|s| !writes.contains(&s.dest) || reads.contains(&s.dest));
    }

    /// The spells in an order where each reading a slot another writes comes before it, if
    /// there is one, those with operations of instruction `at` as late as they can be.
    pub fn order(&self, at: usize) -> Option<Vec<usize>> {
        let n = self.spells.len();
        // `before[i]`: the spells reading what spell `i` writes.
        let before: Vec<Vec<usize>> = (0..n).map(|i| {
            (0..n).filter(|&j| j != i && self.spells[j].inputs.contains(&self.spells[i].dest)).collect()
        }).collect();
        let mut order = Vec::with_capacity(n);
        let mut placed = vec![false; n];
        while order.len() < n {
            let ready = |i: &usize| !placed[*i] && before[*i].iter().all(|&j| placed[j]);
            let next = (0..n).filter(ready).find(|&i| self.spells[i].at != at).or_else(|| (0..n).find(ready))?;
            placed[next] = true;
            order.push(next);
        }
        Some(order)
    }

    pub fn is_empty(&self) -> bool {
        self.spells.is_empty() && self.stores.is_empty()
    }

    /// What to lay out before an op needing `need`, and what stays held, as witchcraft's
    /// invariants have it: the spells whose values it reads, and the spells and stores reading a
    /// register it writes, as it was, before it; then those reading what one of these writes, and
    /// the stores one of these comes after; and every store, if it may touch memory. See Note
    /// [Peephole fusion].
    pub fn split(&self, need: &Need) -> (Spells, Spells) {
        let mut spells: Vec<bool> = self.spells.iter().map(|s| need.reads.contains(&s.dest) || s.inputs.iter().any(|i| need.writes.contains(i))).collect();
        let mut stores: Vec<bool> = self.stores.iter().map(|s| need.memory || s.inputs().any(|i| need.writes.contains(&i))).collect();
        loop {
            let written: Vec<usize> = self.spells.iter().zip(&spells).filter(|(_, laid)| **laid).map(|(s, _)| s.dest).collect();
            let before: Vec<usize> = self.stores.iter().zip(&stores).filter(|(_, laid)| **laid).flat_map(|(s, _)| s.after.iter().copied()).collect();
            let mut more = false;
            for (s, laid) in self.spells.iter().zip(spells.iter_mut()) {
                if !*laid && s.inputs.iter().any(|i| written.contains(i)) {
                    *laid = true;
                    more = true;
                }
            }
            for (s, laid) in self.stores.iter().zip(stores.iter_mut()) {
                if !*laid && (before.contains(&s.id) || s.inputs().any(|i| written.contains(&i))) {
                    *laid = true;
                    more = true;
                }
            }
            if !more {
                break;
            }
        }
        let part = |laid: bool| Spells {
            spells: self.spells.iter().zip(&spells).filter(|(_, l)| **l == laid).map(|(s, _)| s.clone()).collect(),
            stores: self.stores.iter().zip(&stores).filter(|(_, l)| **l == laid).map(|(s, _)| s.clone()).collect(),
            next: self.next,
        };
        (part(true), part(false))
    }

    /// The stores and spells laid out in instruction `at`, in order, with `held` held still: each
    /// one op, and where it can fail, its cold way's materializations of it, those after it and
    /// those held. See Note [Peephole fusion].
    pub fn lay_out(&self, at: usize, held: &Spells) -> Vec<Laid> {
        let order: Vec<&Spell> = self.order(at).expect("held spells are in an order").into_iter().map(|i| &self.spells[i]).collect();
        let mut laid = Vec::with_capacity(self.stores.len() + order.len());
        // The stores first: they read registers as they were before any held operation, and write
        // none. In the order they were held, which each's `after` keeps.
        for store in &self.stores {
            laid.push(Laid { op: store.window.clone(), checked: false, exit: Vec::new(), unknown: Vec::new() });
        }
        for (k, spell) in order.iter().enumerate() {
            let ops = spell.ops();
            if !spell.can_fail() || order[..k].iter().any(|before| before.went_on_from(spell)) {
                laid.push(Laid { op: ops.compute, checked: false, exit: Vec::new(), unknown: Vec::new() });
                continue;
            }
            debug_assert!(order[..k].iter().all(|before| before.at != at), "a spell can fail after one with its instruction's operations");
            // The held stores first, which read registers as they were, then the spells after it
            // and those held, none of which reads what one before it wrote.
            let unwritten = order[k..].iter().copied().chain(&held.spells);
            let exit = held.stores.iter().map(|s| s.window.clone())
                .chain(unwritten.clone().filter_map(|s| if s.at == at { s.before_instruction(at) } else { Some(s) }).map(|s| s.ops().materialize))
                .collect();
            let unknown = unwritten.map(|s| s.dest).collect();
            laid.push(Laid { op: ops.fused, checked: true, exit, unknown });
        }
        laid
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use Operand::{K, Slot};

    fn op(op: Arith, lhs: Operand, rhs: Operand, dest: usize) -> IntOp {
        IntOp { op, lhs, rhs, dest }
    }

    /// Knowing no slot holds a constant.
    fn none(_: usize) -> Option<i32> {
        None
    }

    fn held(spells: &Spells) -> Vec<(&'static str, usize, Vec<usize>)> {
        spells.spells.iter().map(|s| (s.rule(), s.dest, s.inputs.clone())).collect()
    }

    /// Offer each of `ops`, one per instruction from `at`, each held.
    fn hold(spells: &mut Spells, at: usize, ops: &[IntOp]) {
        for (i, o) in ops.iter().enumerate() {
            assert_eq!(spells.offer(o, at + i, none), Offer::Held, "{o:?}");
        }
    }

    /// The ops laid out in instruction `at`: each's name and operands, whether it can fail, and
    /// its cold way's materializations' names and operands.
    fn laid(spells: &Spells, at: usize) -> Vec<(&'static str, Vec<usize>, bool, Vec<(&'static str, Vec<usize>)>)> {
        let named = |w: &Rc<dyn Window>| (w.name(), w.operands().to_vec());
        spells.lay_out(at, &Spells::default()).iter().map(|l| {
            let (name, operands) = named(&l.op);
            (name, operands, l.checked, l.exit.iter().map(named).collect())
        }).collect()
    }

    #[test]
    fn every_prefix_is_a_rule() {
        LazyLock::force(&TRIE);
    }

    #[test]
    fn an_index_computation_is_one_spell_with_its_guard() {
        // s[(p - 1) % 256 + 1], p in slot 5, the key in slot 6, the table in slot 1, the get at
        // instruction 3.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Sub, Slot(5), K(1), 6), op(Arith::Mod, Slot(6), K(256), 6), op(Arith::Add, Slot(6), K(1), 6)]);
        assert!(spells.offer_guard(&crate::generators::InArrayHeld::new(&[1, 6]), 3));
        assert_eq!(held(&spells), [("SUB_MASK_ADD_HELD", 6, vec![5, 1])]);
        // One op; failing, the get runs again with the key as its operations made it.
        assert_eq!(laid(&spells, 3), [("FusedSubMaskAddHeld", vec![1, 5, 6], true, vec![("MaterializeSubMaskAdd", vec![5, 6])])]);
    }

    // An op updating its operand in place, with no way out and touching no memory.
    crate::window::windowed!(Bump, [], [], |owner, state, base| (inout v) {
        let _ = v;
    });

    /// Whether `spells` stay held across `window`, dropping what it overwrites if they do, as the
    /// specializer does.
    fn across(spells: &mut Spells, window: &dyn Window) -> bool {
        if !spells.untouched(window) {
            return false;
        }
        let writes: Vec<usize> = window.operands().iter().zip(window.accesses()).filter(|(_, a)| **a == crate::window::Access::Write).map(|(s, _)| *s).collect();
        spells.drop_overwritten(&writes, &[]);
        true
    }

    #[test]
    fn a_chain_goes_on_across_a_pure_op_off_its_registers() {
        // x = x + 1; y = z; x = x % 256: the move between is held across, and the chain goes on.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(1), K(1), 1)]);
        assert!(across(&mut spells, &crate::generators::Move::new(&[3, 4])));
        hold(&mut spells, 2, &[op(Arith::Mod, Slot(1), K(256), 1)]);
        assert_eq!(held(&spells), [("ADD_MASK", 1, vec![1])]);
    }

    #[test]
    fn an_op_reading_a_held_register_lays_them_out() {
        // x = x + 1; y = x: the move reads what the spell computes.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(1), K(1), 1)]);
        assert!(!across(&mut spells, &crate::generators::Move::new(&[1, 4])));
    }

    #[test]
    fn an_op_writing_a_held_input_lays_them_out() {
        // y = x + 1; x = z: the spell reads x as it was, which the move overwrites.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(1), K(1), 2)]);
        assert!(!across(&mut spells, &crate::generators::Move::new(&[3, 1])));
    }

    #[test]
    fn an_op_overwriting_a_held_register_drops_its_spell() {
        // y = x + 1; y = z; w = v + 2: y's spell is never read, and the other's stays held.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(1), K(1), 2), op(Arith::Add, Slot(5), K(2), 6)]);
        assert!(across(&mut spells, &crate::generators::Move::new(&[3, 2])));
        assert_eq!(held(&spells), [("ADD_", 6, vec![5])]);
        // And by a load writing it, as a frozen table's element.
        assert!(across(&mut spells, &crate::generators::LoadFrozen::new(0, &[6])));
        assert!(spells.is_empty());
    }

    #[test]
    fn an_op_touching_memory_lays_them_out() {
        // Off the held registers, but reading an upvalue's cell, or writing one.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(1), K(1), 1)]);
        assert!(!across(&mut spells, &crate::generators::GetUpval::new(0, 0, &[4])));
        assert!(!across(&mut spells, &crate::generators::SetUpval::new(0, 0, &[4])));
    }

    #[test]
    fn an_op_with_a_way_out_lays_them_out() {
        // A guard off the held registers: its exit would go on with them unwritten.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(1), K(1), 1)]);
        assert!(!across(&mut spells, &crate::generators::EqualsK::new(5, &[3])));
    }

    #[test]
    fn an_op_updating_in_place_lays_them_out() {
        // An exit going on from before it would run it again on its own result.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(1), K(1), 1)]);
        assert!(!across(&mut spells, &Bump::new(&[3])));
    }

    // A store, as one the peephole holds, and one of nil, which it doesn't.
    crate::window::windowed!(writes TestStore, [k: i32], [], |owner, state, base| (table, value) {
        let _ = (owner, table, value, k);
    });
    crate::window::windowed!(writes StoreNil, [k: i32], [], |owner, state, base| (table) {
        let _ = (owner, table, k);
    });

    /// The element of the table in register `table` at `key`.
    fn element(table: usize, key: Operand) -> Element {
        Element { table, key }
    }

    /// How two elements are, as the context would know them knowing only that a register is
    /// itself: one register is one table, and others may be.
    fn alias(a: Element, b: Element) -> Alias {
        match (a.key, b.key) {
            (K(x), K(y)) if x != y => Alias::Disjoint,
            (x, y) if x == y && a.table == b.table => Alias::Same,
            _ => Alias::May,
        }
    }

    /// Hold the store of register `value` into `at`, as instruction `pc`.
    fn store(spells: &mut Spells, at: Element, value: usize, pc: usize) {
        let K(k) = at.key else { panic!("a test stores at a constant key") };
        spells.hold_store(at, Stored::Slot(value), Rc::new(TestStore::new(k, &[at.table, value])), pc, alias);
    }

    /// What a load of `at` becomes: the register forwarded, or the stores laid out before it, by
    /// their keys.
    fn load(spells: &mut Spells, at: Element) -> Result<Stored, Vec<i32>> {
        match spells.load(at, alias) {
            Load::Forward(value) => Ok(value),
            Load::After(stores) => Err(stores.iter().map(|w| w.captures()[0] as i32).collect()),
        }
    }

    #[test]
    fn a_load_of_a_stored_element_is_the_stored_value() {
        // t[1] = x; y = t[1]: no load.
        let mut spells = Spells::default();
        store(&mut spells, element(1, K(1)), 5, 0);
        assert_eq!(load(&mut spells, element(1, K(1))), Ok(Stored::Slot(5)));
        assert_eq!(spells.stores.len(), 1, "a load leaves the store held");
    }

    #[test]
    fn a_store_overwritten_unread_is_dead() {
        // t[1] = x; t[1] = y: only the second is laid out.
        let mut spells = Spells::default();
        store(&mut spells, element(1, K(1)), 5, 0);
        store(&mut spells, element(1, K(1)), 6, 1);
        assert_eq!(spells.stores.iter().map(|s| s.value).collect::<Vec<_>>(), [Stored::Slot(6)]);
        assert_eq!(spells.lay_out(2, &Spells::default()).len(), 1);
    }

    /// What `split` lays out for `need`, and what it keeps: each's spells' registers and stores'
    /// keys.
    fn split(spells: &Spells, reads: &[usize], writes: &[usize], memory: bool) -> ((Vec<usize>, Vec<Operand>), (Vec<usize>, Vec<Operand>)) {
        let need = Need { reads: reads.to_vec(), writes: writes.to_vec(), memory };
        let (laid, kept) = spells.split(&need);
        let regs = |s: &Spells| (s.spells.iter().map(|s| s.dest).collect(), s.stores.iter().map(|s| s.cell.key).collect());
        (regs(&laid), regs(&kept))
    }

    #[test]
    fn an_op_reading_a_spell_lays_out_only_it() {
        // x = x + 1; y = y - 2; t[1] = z; then an op reading x: y's spell and the store stay held.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(1), K(1), 1), op(Arith::Sub, Slot(2), K(2), 2)]);
        store(&mut spells, element(4, K(1)), 5, 2);
        assert_eq!(split(&spells, &[1], &[6], false), ((vec![1], vec![]), (vec![2], vec![K(1)])));
    }

    #[test]
    fn an_op_writing_what_a_spell_reads_lays_it_out() {
        // y = x + 1, then an op writing x: y's spell reads x as it was, so it goes first; and so
        // does a store of x.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(1), K(1), 2), op(Arith::Sub, Slot(3), K(2), 3)]);
        store(&mut spells, element(4, K(1)), 1, 1);
        assert_eq!(split(&spells, &[], &[1], false), ((vec![2], vec![K(1)]), (vec![3], vec![])));
    }

    #[test]
    fn what_reads_a_laid_out_spells_register_is_laid_out_before_it() {
        // y = x + 1; x = x * 2; t[1] = x: an op reading x lays out x's spell, which writes x,
        // which y's spell and the store read as it was.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(1), K(1), 2), op(Arith::Mul, Slot(1), K(2), 1)]);
        store(&mut spells, element(4, K(1)), 1, 2);
        let ((mut laid, stores), kept) = split(&spells, &[1], &[6], false);
        laid.sort();
        assert_eq!((laid, stores, kept), (vec![1, 2], vec![K(1)], (vec![], vec![])));
    }

    #[test]
    fn an_op_touching_memory_lays_out_the_stores() {
        // t[1] = x; u[1] = y, the second after the first as they may be one element; then an op
        // reading memory: both, and the spell stays held. Laying out the second alone lays out the
        // first.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(1), K(1), 1)]);
        store(&mut spells, element(4, K(1)), 5, 1);
        store(&mut spells, element(6, K(1)), 7, 2);
        assert_eq!(split(&spells, &[], &[], true), ((vec![], vec![K(1), K(1)]), (vec![1], vec![])));
        assert_eq!(split(&spells, &[], &[7], false).0.1, vec![K(1), K(1)]);
    }

    #[test]
    fn an_exit_writes_what_is_held_still() {
        // x = x + 1, laid out; y = y + 2 and t[1] = z held still: where x's spell fails, its exit
        // writes the store, then x and y as their operations would.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(1), K(1), 1), op(Arith::Add, Slot(2), K(2), 2)]);
        store(&mut spells, element(4, K(1)), 5, 2);
        let (laid, kept) = spells.split(&Need { reads: vec![1], writes: vec![], memory: false });
        let out = laid.lay_out(3, &kept);
        assert_eq!(out.len(), 1);
        assert!(out[0].checked);
        assert_eq!(out[0].exit.iter().map(|w| (w.name(), w.operands().to_vec())).collect::<Vec<_>>(),
            [("TestStore", vec![4, 5]), ("MaterializeAdd", vec![1, 1]), ("MaterializeAdd", vec![2, 2])]);
        assert_eq!(out[0].unknown, [1, 2]);
    }

    #[test]
    fn a_store_about_to_run_kills_one_held_into_its_element() {
        // t[1] = x; t[1] = y, the second laid out as it is: the first is dead whether or not the
        // second is held, and t[2]'s store stays held.
        let mut spells = Spells::default();
        store(&mut spells, element(1, K(1)), 5, 0);
        store(&mut spells, element(1, K(2)), 6, 1);
        assert_eq!(spells.kill_stores(element(1, K(1)), alias), 1);
        assert_eq!(spells.stores.iter().map(|s| s.cell).collect::<Vec<_>>(), [element(1, K(2))]);
    }

    #[test]
    fn stores_to_different_keys_are_apart() {
        // t[1] = x; u[2] = y; z = t[1]: u may be t, but its key isn't 1.
        let mut spells = Spells::default();
        store(&mut spells, element(1, K(1)), 5, 0);
        store(&mut spells, element(2, K(2)), 6, 1);
        assert_eq!(load(&mut spells, element(1, K(1))), Ok(Stored::Slot(5)));
    }

    #[test]
    fn a_load_that_may_alias_comes_after_the_stores() {
        // t[1] = x; u[1] = y; t[2] = w; z = u[1]: t may be u, so its store may be the element
        // too; the store to t[2] can't be, and stays held.
        let mut spells = Spells::default();
        store(&mut spells, element(1, K(1)), 5, 0);
        store(&mut spells, element(2, K(1)), 6, 1);
        store(&mut spells, element(1, K(2)), 7, 2);
        assert_eq!(load(&mut spells, element(2, K(1))), Err(vec![1, 1]));
        assert_eq!(spells.stores.len(), 1);
        assert_eq!(spells.stores[0].cell, element(1, K(2)));
    }

    #[test]
    fn a_store_that_may_alias_keeps_the_one_before() {
        // t[1] = x; u[1] = y: u may be t, so the first isn't dead, and comes first.
        let mut spells = Spells::default();
        store(&mut spells, element(1, K(1)), 5, 0);
        store(&mut spells, element(2, K(1)), 6, 1);
        assert_eq!(spells.stores.len(), 2);
        let laid: Vec<i32> = spells.lay_out(2, &Spells::default()).iter().map(|l| l.op.operands()[1] as i32).collect();
        assert_eq!(laid, [5, 6]);
    }

    #[test]
    fn a_repeated_load_across_a_store_of_nil_loads_again() {
        // t[2] = x; y = t[2]; t[3] = nil; z = t[2]. The first load is the stored value. The store
        // of nil may shorten the array part, so it isn't held: it, and what is held, are laid out
        // before it, and the guard on the second load's key then reads the part's length after
        // it, as the load does its element.
        let mut spells = Spells::default();
        store(&mut spells, element(1, K(2)), 5, 0);
        assert_eq!(load(&mut spells, element(1, K(2))), Ok(Stored::Slot(5)));
        assert!(!spells.untouched(&StoreNil::new(3, &[1])), "a store of nil lays out what is held");
        let laid = spells.lay_out(2, &Spells::default());
        assert_eq!(laid.iter().map(|l| l.op.name()).collect::<Vec<_>>(), ["TestStore"]);
        let mut after = Spells::default();
        assert!(after.across_guard(&crate::generators::InArrayK::new(2, &[1]), 3));
        assert_eq!(load(&mut after, element(1, K(2))), Err(vec![]), "loaded, not forwarded");
    }

    #[test]
    fn a_guard_on_a_key_keeps_stores_held() {
        // t[1] = x, then the guard that t[2] is in t's array part: it reads only the part's
        // length and kind, which the store, of a value that isn't nil, leaves as they were.
        let mut spells = Spells::default();
        store(&mut spells, element(1, K(1)), 5, 0);
        assert!(spells.across_guard(&crate::generators::InArrayK::new(2, &[1]), 1));
    }

    #[test]
    fn interleaved_chains_are_held_apart() {
        // A B C D: x = x + 1; y = y - 2; x = x % 256; y = y % 16, on slots 1 and 2.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(1), K(1), 1), op(Arith::Sub, Slot(2), K(2), 2), op(Arith::Mod, Slot(1), K(256), 1), op(Arith::Mod, Slot(2), K(16), 2)]);
        assert_eq!(held(&spells), [("ADD_MASK", 1, vec![1]), ("SUB_MASK", 2, vec![2])]);
        // Laid out by a later instruction: where the first fails, both are written as the
        // operations would; where the second does, the first is written already.
        assert_eq!(laid(&spells, 4), [
            ("FusedAddMask", vec![1, 1], true, vec![("MaterializeAddMask", vec![1, 1]), ("MaterializeSubMask", vec![2, 2])]),
            ("FusedSubMask", vec![2, 2], true, vec![("MaterializeSubMask", vec![2, 2])]),
        ]);
    }

    #[test]
    fn a_value_read_into_another_slot_makes_a_spell_of_it() {
        // acc = acc + t * 256, t in slot 9 multiplied in place, acc in slot 8: the sum is a spell of
        // t's, t's held too; then t is overwritten unread, so only the sum's is left.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Mul, Slot(9), K(256), 9), op(Arith::Add, Slot(8), Slot(9), 8)]);
        assert_eq!(held(&spells), [("MUL_", 9, vec![9]), ("MUL_RR_ADD", 8, vec![9, 8])]);
        // The sum reads t as it was: it comes first, and checks t's too, so t's only computes.
        assert_eq!(spells.order(2), Some(vec![1, 0]));
        assert_eq!(laid(&spells, 2), [
            ("FusedMulPairAdd", vec![9, 8, 8], true, vec![("MaterializeMulPairAdd", vec![9, 8, 8]), ("MaterializeMul", vec![9, 9])]),
            ("ComputeMul", vec![9, 9], false, vec![]),
        ]);
        hold(&mut spells, 2, &[op(Arith::Add, Slot(3), K(1), 9)]);
        assert_eq!(held(&spells), [("MUL_RR_ADD", 8, vec![9, 8]), ("ADD_", 9, vec![3])]);
        assert_eq!(spells.order(3), Some(vec![0, 1]));
    }

    #[test]
    fn spells_reading_a_slot_come_before_the_one_writing_it() {
        // a = b + 1, then b = (a) % 256, a spell of a's into b: a's reads b as it was, so it comes
        // first.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(2), K(1), 1), op(Arith::Mod, Slot(1), K(256), 2)]);
        assert_eq!(held(&spells), [("ADD_", 1, vec![2]), ("ADD_MASK", 2, vec![2])]);
        assert_eq!(spells.order(2), Some(vec![0, 1]));
        // Writing a slot a spell reads, from another, is ordered after it too.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(2), K(1), 1), op(Arith::Sub, Slot(3), K(4), 2)]);
        assert_eq!(spells.order(2), Some(vec![0, 1]));
    }

    #[test]
    fn the_instructions_own_spell_fails_last() {
        // x = y + 1 at 0, then z = w - 2 at 1, laid out by instruction 1 itself: z's comes last,
        // failing to instruction 1 run again, so only x's, from instruction 0, is written; z's
        // operation runs again.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(2), K(1), 1), op(Arith::Sub, Slot(4), K(2), 3)]);
        assert_eq!(laid(&spells, 1), [
            ("FusedAdd", vec![2, 1], true, vec![("MaterializeAdd", vec![2, 1])]),
            ("FusedSub", vec![4, 3], true, vec![]),
        ]);
        // Going on in it, from instruction 0: written as it was before.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(2), K(1), 1), op(Arith::Mod, Slot(1), K(256), 1)]);
        assert_eq!(laid(&spells, 1), [("FusedAddMask", vec![2, 1], true, vec![("MaterializeAdd", vec![2, 1])])]);
    }

    #[test]
    fn a_spell_needing_another_after_it_is_held_only_if_it_checks_it() {
        // a = s + 1 at 0, s = s + 2 at 1, then a = a % 256 at 2: a's reads s as it was, so s's
        // comes after it, though its instruction is earlier, and s's isn't a's chain.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(5), K(1), 1), op(Arith::Add, Slot(5), K(2), 5)]);
        assert_eq!(spells.offer(&op(Arith::Mod, Slot(1), K(256), 1), 2, none), Offer::Flush);
    }

    #[test]
    fn operations_of_constants_fold() {
        // pc in slot 1 known to be 255: pc = (pc + 1) % 256 folds to 0, and what reads it then
        // reads a constant; a chain from it is a constant store.
        let known = |slot: usize| (slot == 1).then_some(255);
        let mut spells = Spells::default();
        assert_eq!(spells.offer(&op(Arith::Add, Slot(1), K(1), 2), 0, known), Offer::Folded(256));
        assert_eq!(spells.offer(&op(Arith::Mod, Slot(2), K(256), 2), 1, |slot| (slot == 2).then_some(256)), Offer::Folded(0));
        assert_eq!(held(&spells), [("CONST_", 2, vec![])]);
        assert_eq!(laid(&spells, 2), [("LoadK", vec![2], false, vec![])]);
        // One constant operand is a step.
        let mut spells = Spells::default();
        assert_eq!(spells.offer(&op(Arith::Add, Slot(3), Slot(1), 4), 0, known), Offer::Held);
        assert_eq!(held(&spells), [("ADD_", 4, vec![3])]);
        // What doesn't fit isn't folded.
        assert_eq!(Spells::default().offer(&op(Arith::Add, Slot(1), K(i32::MAX), 2), 0, known), Offer::Refused);
        assert_eq!(Spells::default().offer(&op(Arith::Mul, Slot(1), K(0), 2), 0, |_| Some(-3)), Offer::Refused);
    }

    #[test]
    fn the_floor_of_a_quotient_is_a_floored_division() {
        // math.floor(n / 256) with n in slot 1, the quotient into slot 2 and its floor into 3: a
        // shift, the quotient held too, a double if anything reads it.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Div, Slot(1), K(256), 2), op(Arith::Floor, Slot(2), K(0), 3)]);
        assert_eq!(held(&spells), [("DIV_", 2, vec![1]), ("DIV_FLOOR", 3, vec![1])]);
        assert_eq!(laid(&spells, 2), [("ComputeDiv", vec![1, 2], false, vec![]), ("ComputeDivFloorShift", vec![1, 3], false, vec![])]);
        // By a constant that isn't a power of two: the floored division.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Div, Slot(1), K(10), 2), op(Arith::Floor, Slot(2), K(0), 3)]);
        assert_eq!(spells.lay_out(2, &Spells::default()).iter().map(|l| l.op.name()).collect::<Vec<_>>(), ["ComputeDiv", "ComputeDivFloor"]);
        // A floor of anything else isn't held.
        assert_eq!(Spells::default().offer(&op(Arith::Floor, Slot(2), K(0), 3), 0, none), Offer::Refused);
    }

    #[test]
    fn dead_values_are_never_laid_out() {
        // A chain overwritten unread: t = x + 1; t = t % 256; then t = y - 2.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(1), K(1), 3), op(Arith::Mod, Slot(3), K(256), 3), op(Arith::Sub, Slot(2), K(2), 3)]);
        assert_eq!(held(&spells), [("SUB_", 3, vec![2])]);
        // Among live ones: x = x + 1 lives on, t = y + 2 doesn't, overwritten by t = z + 5.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(1), K(1), 1), op(Arith::Add, Slot(2), K(2), 3), op(Arith::Add, Slot(4), K(5), 3)]);
        assert_eq!(held(&spells), [("ADD_", 1, vec![1]), ("ADD_", 3, vec![4])]);
        // Overwritten by what can't be held: dropped, nothing left to lay out.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(1), K(1), 3)]);
        assert_eq!(spells.offer(&op(Arith::Mul, Slot(2), K(-2), 3), 1, none), Offer::Refused);
        assert!(spells.is_empty());
        // Overwritten by something else laid out, as a constant loaded into it; one reading it
        // keeps it.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(1), K(1), 3)]);
        let mut kept = spells.clone();
        kept.drop_overwritten(&[3], &[3]);
        assert_eq!(kept.spells.len(), 1);
        spells.drop_overwritten(&[3], &[]);
        assert!(spells.is_empty());
    }

    #[test]
    fn what_lays_out_the_spells() {
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(1), K(1), 3)]);
        // Reading a held value with no rule going on.
        assert_eq!(spells.clone().offer(&op(Arith::Mul, Slot(3), K(-2), 3), 1, none), Offer::Flush);
        assert_eq!(spells.clone().offer(&op(Arith::Mod, Slot(3), K(7), 4), 1, none), Offer::Flush);
        // Reading two held values.
        let mut two = spells.clone();
        hold(&mut two, 1, &[op(Arith::Add, Slot(5), K(1), 4)]);
        assert_eq!(two.offer(&op(Arith::Add, Slot(3), Slot(4), 6), 2, none), Offer::Flush);
        // A product that could be -0, with nothing held, is refused.
        assert_eq!(Spells::default().offer(&op(Arith::Mul, Slot(3), K(-2), 3), 0, none), Offer::Refused);
        // A guard on a key held is joined, ending its spell; on another, not.
        assert!(!spells.joins_guard(&crate::generators::InArray::new(&[2, 5]), 1));
        assert!(spells.offer_guard(&crate::generators::InArray::new(&[2, 3]), 1));
        assert_eq!(spells.offer(&op(Arith::Add, Slot(3), K(1), 3), 2, none), Offer::Flush);
    }

    #[test]
    fn a_pair_and_its_steps() {
        // (p + k + 1) % 256 into slot 3: p in slot 1, k in slot 2.
        let mut spells = Spells::default();
        hold(&mut spells, 0, &[op(Arith::Add, Slot(1), Slot(2), 3), op(Arith::Add, Slot(3), K(1), 3), op(Arith::Mod, Slot(3), K(256), 3)]);
        assert_eq!(held(&spells), [("RR_ADD_ADD_MASK", 3, vec![1, 2])]);
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
            Arith::Div => l / r,
            Arith::Floor => l.floor(),
        }
    }

    /// Whether a double is a value of the integer encoding: whole, in range, and not -0.
    fn in_encoding(v: f64) -> Option<i32> {
        (v.fract() == 0.0 && v >= i32::MIN as f64 && v <= i32::MAX as f64 && v.to_bits() != (-0.0f64).to_bits()).then_some(v as i32)
    }

    #[test]
    fn steps_compute_as_lua_does() {
        // Each step and sum or difference against Lua's doubles, on edge values: its result where
        // that is an integer, else none, and the same where it fits, unchecked.
        let edges = [0, 1, -1, 255, 256, -256, i32::MAX, i32::MIN, 1 << 30, -(1 << 30)];
        for &x in &edges {
            for k in [1, 2, 7, 256, 65536, -3, i32::MAX] {
                for (kind, s) in [(Arith::Add, ADD), (Arith::Sub, SUB), (Arith::Mul, MUL)] {
                    if kind == Arith::Mul && k <= 0 {
                        continue;
                    }
                    let expected = in_encoding(lua(&op(kind, Slot(0), K(k), 0), &[x as f64]));
                    let (checked, unchecked) = match s {
                        ADD => (step::<ADD>(x, k), wrapping::<ADD>(x, k)),
                        SUB => (step::<SUB>(x, k), wrapping::<SUB>(x, k)),
                        _ => (step::<MUL>(x, k), wrapping::<MUL>(x, k)),
                    };
                    assert_eq!(checked, expected, "{kind:?} {x} {k}");
                    if let Some(v) = checked {
                        assert_eq!(unchecked, v);
                    }
                }
                for (kind, o) in [(Arith::Add, ADD), (Arith::Sub, SUB)] {
                    let expected = in_encoding(lua(&op(kind, Slot(0), Slot(1), 0), &[x as f64, k as f64]));
                    let (checked, unchecked) = if o == ADD { (pair::<ADD>(x, k), wrapping_pair::<ADD>(x, k)) } else { (pair::<SUB>(x, k), wrapping_pair::<SUB>(x, k)) };
                    assert_eq!(checked, expected, "{kind:?} {x} {k}");
                    if let Some(v) = checked {
                        assert_eq!(unchecked, v);
                    }
                }
            }
            for k in [1, 2, 256, 1 << 30] {
                assert_eq!(step::<MASK>(x, k - 1), in_encoding(lua(&op(Arith::Mod, Slot(0), K(k), 0), &[x as f64])), "{x} % {k}");
            }
        }
    }
}
