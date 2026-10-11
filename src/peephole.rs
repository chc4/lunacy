//! Fusing integer arithmetic into window ops, per value. See Note [Peephole fusion].

use std::rc::Rc;
use std::sync::LazyLock;

use crate::lboxed::LBoxed;
use crate::vm::{LValue, Opcode};
#[cfg(feature = "unreachable")]
use crate::unreachable;
use crate::window::{windowed, Window};

// Note [Peephole fusion]
// ~~~~~~~~~~~~~~~~~~~~~~
// Each integer operation in the integer encoding checks its own result fits, and boxes it, though
// the next often only reads it to compute another: `(p - 1) % 256 + 1` checks and boxes three
// times. A chain of integer operations on one value can instead be laid out as one check and one
// computation.
//
// Every generator's yields pass through a peephole as the specializer lays them out. An integer
// operation's generator says what its window computes before yielding it, and the peephole holds it
// instead of laying it out, as a spell: the computation of the slot it writes, suspended. The
// generator goes on as if the operation took its hot path, and so does the code after it, whichever
// instructions those are. An operation reading a held value joins that value's spell, if a rule
// matches the chain it makes; anything writing a held value no one read drops its spell; a guard
// of whether a held value is a key in a table's array part (and the element there not nil), which a
// get or set yields before reading it, joins the spell too, as passed, and ends it. Spells of other
// values are held alongside, so chains of different values interleave.
//
// What the peephole holds it lays out when anything would read a held value but can't join its
// spell, would write a value a spell reads, or would lay out code: every spell at once. Each is a
// check, which computes it and tests every step fits, as the operations would, and the guard it ends
// in passes, and a computation, which writes it: every check comes first, so where one fails nothing
// has been written, and the code goes on from the first operation held, laid out as it would have
// been there, the values the operations read as they were. Where all pass, the computations write
// the values and the code goes on where the peephole laid them out.
//
// The rules are the chains code computes keys and bytes with, and every one of their prefixes, so a
// spell is always one. A spell's operations make no -0, so a step that fits is the double its
// operation would have computed. A spell that can't fail, only masks, has no check.

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

    /// Its slot operands.
    fn reads(&self) -> impl Iterator<Item = usize> {
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

/// What a spell's windows take: its constants, in order, and its registers.
#[derive(Clone, Debug)]
pub struct Matched {
    pub ks: Vec<i32>,
    pub lhs: usize,
    pub rhs: Option<usize>,
    pub table: Option<usize>,
    pub dest: usize,
}

/// A rule: the chain it matches, and its check and computation.
pub struct Rule {
    pub name: &'static str,
    pub pattern: &'static [Sym],
    pub make: fn(&Matched) -> (Rc<dyn Window>, Rc<dyn Window>),
}

/// The next constant of iterator `$ks` as a hole, for each `$k`.
macro_rules! holes {
    ($ks:ident;) => { [0u64; 0] };
    ($ks:ident; $($k:ident)*) => { [$({ let _ = stringify!($k); (*$ks.next().unwrap()) as u32 as u64 }),*] };
}

/// A rule `$rule`, with check `$check` and computation `$compute`, over a chain of steps of a
/// register by constants `[S k, ..]`, ending in a guard `in G` or not; first a sum or difference
/// of two registers `rr O`; or one step then a sum or difference with another register.
macro_rules! rule {
    ($rule:ident, $check:ident, $compute:ident = [$($s:ident $k:ident),+]) => {
        windowed!(guard $check, [$($k: u64),+], [], |owner, state, base| (lhs) {
            (|| -> Option<i32> { let x = lhs.as_int(); $(let x = step::<$s>(x, $k as i32)?;)+ Some(x) })().is_some()
        });
        windowed!($compute, [$($k: u64),+], [], |owner, state, base, tag| (lhs, out dest) {
            let x = lhs.as_int();
            $(let x = wrapping::<$s>(x, $k as i32);)+
            *dest = LBoxed::from_int_tagged(x, tag);
        });
        const $rule: Rule = Rule { name: stringify!($rule), pattern: &[$(Sym::K($s)),+], make: |m| {
            let (mut first, mut second) = (m.ks.iter(), m.ks.iter());
            let [$($k),+] = holes!(first; $($k)+);
            let check = Rc::new($check::new($($k,)+ &[m.lhs])) as Rc<dyn Window>;
            let [$($k),+] = holes!(second; $($k)+);
            (check, Rc::new($compute::new($($k,)+ &[m.lhs, m.dest])) as Rc<dyn Window>)
        }};
    };
    ($rule:ident, $check:ident, $compute:ident = [$($s:ident $k:ident),+] in $g:ident) => {
        windowed!(guard $check, [$($k: u64),+], [], |owner, state, base| (table, lhs) {
            (|| -> Option<i32> { let x = lhs.as_int(); $(let x = step::<$s>(x, $k as i32)?;)+ Some(x) })()
                .is_some_and(|x| passes::<$g>(owner, table, x))
        });
        windowed!($compute, [$($k: u64),+], [], |owner, state, base, tag| (lhs, out dest) {
            let x = lhs.as_int();
            $(let x = wrapping::<$s>(x, $k as i32);)+
            *dest = LBoxed::from_int_tagged(x, tag);
        });
        const $rule: Rule = Rule { name: stringify!($rule), pattern: &[$(Sym::K($s),)+ Sym::Guard($g)], make: |m| {
            let (mut first, mut second) = (m.ks.iter(), m.ks.iter());
            let [$($k),+] = holes!(first; $($k)+);
            let check = Rc::new($check::new($($k,)+ &[m.table.unwrap(), m.lhs])) as Rc<dyn Window>;
            let [$($k),+] = holes!(second; $($k)+);
            (check, Rc::new($compute::new($($k,)+ &[m.lhs, m.dest])) as Rc<dyn Window>)
        }};
    };
    ($rule:ident, $check:ident, $compute:ident = rr $o:ident [$($s:ident $k:ident),*]) => {
        windowed!(guard $check, [$($k: u64),*], [], |owner, state, base| (lhs, rhs) {
            (|| -> Option<i32> {
                let x = pair::<$o>(lhs.as_int(), rhs.as_int())?;
                $(let x = step::<$s>(x, $k as i32)?;)*
                Some(x)
            })().is_some()
        });
        windowed!($compute, [$($k: u64),*], [], |owner, state, base, tag| (lhs, rhs, out dest) {
            let x = wrapping_pair::<$o>(lhs.as_int(), rhs.as_int());
            $(let x = wrapping::<$s>(x, $k as i32);)*
            *dest = LBoxed::from_int_tagged(x, tag);
        });
        const $rule: Rule = Rule { name: stringify!($rule), pattern: &[Sym::RR($o), $(Sym::K($s)),*], make: |m| {
            #[allow(unused_mut, unused_variables)]
            let (mut first, mut second) = (m.ks.iter(), m.ks.iter());
            let [$($k),*] = holes!(first; $($k)*);
            let check = Rc::new($check::new($($k,)* &[m.lhs, m.rhs.unwrap()])) as Rc<dyn Window>;
            let [$($k),*] = holes!(second; $($k)*);
            (check, Rc::new($compute::new($($k,)* &[m.lhs, m.rhs.unwrap(), m.dest])) as Rc<dyn Window>)
        }};
    };
    ($rule:ident, $check:ident, $compute:ident = [$s:ident $k:ident] rr $o:ident) => {
        windowed!(guard $check, [$k: u64], [], |owner, state, base| (lhs, rhs) {
            (|| -> Option<i32> { pair::<$o>(step::<$s>(lhs.as_int(), $k as i32)?, rhs.as_int()) })().is_some()
        });
        windowed!($compute, [$k: u64], [], |owner, state, base, tag| (lhs, rhs, out dest) {
            let x = wrapping_pair::<$o>(wrapping::<$s>(lhs.as_int(), $k as i32), rhs.as_int());
            *dest = LBoxed::from_int_tagged(x, tag);
        });
        const $rule: Rule = Rule { name: stringify!($rule), pattern: &[Sym::K($s), Sym::RR($o)], make: |m| {
            let k = m.ks[0] as u32 as u64;
            (Rc::new($check::new(k, &[m.lhs, m.rhs.unwrap()])) as Rc<dyn Window>,
             Rc::new($compute::new(k, &[m.lhs, m.rhs.unwrap(), m.dest])) as Rc<dyn Window>)
        }};
    };
}

// uxn.lua's: `s[p + 1]`, `(p - 1) % 256 + 1`, `(pc + 1) % 65536 + 1`, `t % 256 + 1`, `(t + 128) % 256 -
// 128`, `(t + 1) % 256`, `(p + k) % 256`, `(p + k + 1) % 256`, `(p + k - 1) % 256`, `n * 256 + t`,
// keys checked as reads (`InArrayHeld`) or writes (`InArray`), and every prefix.
rule!(ADD_, CheckAdd, ComputeAdd = [ADD a]);
rule!(SUB_, CheckSub, ComputeSub = [SUB a]);
rule!(MUL_, CheckMul, ComputeMul = [MUL a]);
rule!(MASK_, CheckMask, ComputeMask = [MASK a]);
rule!(SUB_MASK, CheckSubMask, ComputeSubMask = [SUB a, MASK b]);
rule!(ADD_MASK, CheckAddMask, ComputeAddMask = [ADD a, MASK b]);
rule!(MASK_ADD, CheckMaskAdd, ComputeMaskAdd = [MASK a, ADD b]);
rule!(SUB_MASK_ADD, CheckSubMaskAdd, ComputeSubMaskAdd = [SUB a, MASK b, ADD c]);
rule!(ADD_MASK_ADD, CheckAddMaskAdd, ComputeAddMaskAdd = [ADD a, MASK b, ADD c]);
rule!(ADD_MASK_SUB, CheckAddMaskSub, ComputeAddMaskSub = [ADD a, MASK b, SUB c]);
rule!(ADD_IN, CheckAddIn, ComputeAddIn = [ADD a] in IN_ARRAY);
rule!(ADD_HELD, CheckAddHeld, ComputeAddHeld = [ADD a] in HELD);
rule!(MASK_ADD_IN, CheckMaskAddIn, ComputeMaskAddIn = [MASK a, ADD b] in IN_ARRAY);
rule!(MASK_ADD_HELD, CheckMaskAddHeld, ComputeMaskAddHeld = [MASK a, ADD b] in HELD);
rule!(SUB_MASK_ADD_IN, CheckSubMaskAddIn, ComputeSubMaskAddIn = [SUB a, MASK b, ADD c] in IN_ARRAY);
rule!(SUB_MASK_ADD_HELD, CheckSubMaskAddHeld, ComputeSubMaskAddHeld = [SUB a, MASK b, ADD c] in HELD);
rule!(ADD_MASK_ADD_IN, CheckAddMaskAddIn, ComputeAddMaskAddIn = [ADD a, MASK b, ADD c] in IN_ARRAY);
rule!(ADD_MASK_ADD_HELD, CheckAddMaskAddHeld, ComputeAddMaskAddHeld = [ADD a, MASK b, ADD c] in HELD);
rule!(RR_ADD, CheckPairAdd, ComputePairAdd = rr ADD []);
rule!(RR_ADD_MASK, CheckPairAddMask, ComputePairAddMask = rr ADD [MASK a]);
rule!(RR_ADD_ADD, CheckPairAddAdd, ComputePairAddAdd = rr ADD [ADD a]);
rule!(RR_ADD_ADD_MASK, CheckPairAddAddMask, ComputePairAddAddMask = rr ADD [ADD a, MASK b]);
rule!(RR_ADD_SUB, CheckPairAddSub, ComputePairAddSub = rr ADD [SUB a]);
rule!(RR_ADD_SUB_MASK, CheckPairAddSubMask, ComputePairAddSubMask = rr ADD [SUB a, MASK b]);
rule!(MUL_RR_ADD, CheckMulPairAdd, ComputeMulPairAdd = [MUL a] rr ADD);

/// Every rule.
pub static RULES: &[Rule] = &[
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
    /// The slots it reads, as they were before it.
    pub inputs: Vec<usize>,
    matched: Matched,
    /// Ended in a guard.
    closed: bool,
}

impl Spell {
    /// The spell `op` begins, if a rule begins with it.
    fn start(op: &IntOp) -> Option<Spell> {
        let (sym, matched, inputs) = if let Some((sym, slot, k)) = op.step() {
            (sym, Matched { ks: vec![k], lhs: slot, rhs: None, table: None, dest: op.dest }, vec![slot])
        } else {
            let (sym, l, r) = op.pair()?;
            (sym, Matched { ks: Vec::new(), lhs: l, rhs: Some(r), table: None, dest: op.dest }, vec![l, r])
        };
        let node = TRIE.step(0, sym)?;
        Some(Spell { node, dest: op.dest, inputs, matched, closed: false })
    }

    /// Whether `op`, reading this spell's value, joins it: stepping the value in place, as a rule
    /// goes on.
    fn join(&mut self, op: &IntOp) -> bool {
        if self.closed || op.dest != self.dest {
            return false;
        }
        if let Some((sym, slot, k)) = op.step() {
            let Some(node) = (slot == self.dest).then(|| TRIE.step(self.node, sym)).flatten() else { return false };
            self.node = node;
            self.matched.ks.push(k);
            return true;
        }
        // A sum or difference of the value and another register, which the spell reads too.
        let Some((sym, l, r)) = op.pair() else { return false };
        let Some(node) = (l == self.dest && r != self.dest && self.matched.rhs.is_none()).then(|| TRIE.step(self.node, sym)).flatten() else { return false };
        self.node = node;
        self.matched.rhs = Some(r);
        self.inputs.push(r);
        true
    }

    /// Whether guard `kind` of `table` on this spell's value joins it, ending it.
    fn join_guard(&mut self, kind: u8, table: usize) -> bool {
        let Some(node) = (!self.closed && table != self.dest).then(|| TRIE.step(self.node, Sym::Guard(kind))).flatten() else { return false };
        self.node = node;
        self.matched.table = Some(table);
        self.inputs.push(table);
        self.closed = true;
        true
    }

    /// Its rule's check and computation.
    pub fn windows(&self) -> (Rc<dyn Window>, Rc<dyn Window>) {
        let rule = &RULES[TRIE.rule[self.node].expect("a spell is a rule")];
        (rule.make)(&self.matched)
    }

    /// Whether its check can fail: a step but a mask's, or a guard. One that can't is never laid
    /// out, nor can its stencil be, its test folded away.
    pub fn can_fail(&self) -> bool {
        RULES[TRIE.rule[self.node].expect("a spell is a rule")].pattern.iter().any(|&sym| sym != Sym::K(MASK))
    }

    /// Its rule's name.
    pub fn rule(&self) -> &'static str {
        RULES[TRIE.rule[self.node].expect("a spell is a rule")].name
    }
}

/// What the peephole makes of an operation offered to it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Offer {
    /// It is held, in a spell.
    Held,
    /// Lay out every spell, then offer it again.
    Flush,
    /// It can't be held, with nothing held.
    Refused,
}

/// The spells the peephole holds, one per slot. See Note [Peephole fusion].
#[derive(Clone, Debug, Default)]
pub struct Spells {
    pub spells: Vec<Spell>,
}

impl Spells {
    /// Offer integer operation `op`: joining the spell of the value it reads, or beginning its own.
    pub fn offer(&mut self, op: &IntOp) -> Offer {
        let held = |slot: usize| self.spells.iter().position(|s| s.dest == slot);
        // Reading a held value: joining its spell, else they are laid out first.
        let read: Vec<usize> = op.reads().filter_map(held).collect();
        if let Some(&i) = read.first() {
            let others = read.iter().any(|&j| j != i) || self.spells.iter().enumerate().any(|(j, s)| j != i && s.inputs.contains(&op.dest));
            if !others && self.spells[i].join(op) {
                return Offer::Held;
            }
            return Offer::Flush;
        }
        // Writing a value a spell reads: they are laid out first.
        if self.spells.iter().any(|s| s.inputs.contains(&op.dest)) {
            return Offer::Flush;
        }
        let Some(spell) = Spell::start(op) else {
            // It is laid out as it is: what it overwrites unread isn't, and the rest first.
            self.drop_overwritten(&[op.dest], &[]);
            return if self.spells.is_empty() { Offer::Refused } else { Offer::Flush };
        };
        // A held value overwritten that nothing read.
        self.spells.retain(|s| s.dest != op.dest);
        self.spells.push(spell);
        Offer::Held
    }

    /// Offer the guard `test`, held as passed: joining the spell of the key it tests.
    pub fn offer_guard(&mut self, test: &dyn Window) -> bool {
        let Some((kind, table, key)) = guard(test) else { return false };
        if self.spells.iter().any(|s| s.dest == table) {
            return false;
        }
        self.spells.iter_mut().find(|s| s.dest == key).is_some_and(|s| s.join_guard(kind, table))
    }

    /// Drop the spells of slots `writes` that something about to be laid out writes, reading
    /// only `reads`: their values are never read.
    pub fn drop_overwritten(&mut self, writes: &[usize], reads: &[usize]) {
        self.spells.retain(|s| !writes.contains(&s.dest) || reads.contains(&s.dest));
    }

    /// Whether the guard `test` would join a spell.
    pub fn joins_guard(&self, test: &dyn Window) -> bool {
        self.clone().offer_guard(test)
    }

    pub fn is_empty(&self) -> bool {
        self.spells.is_empty()
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
    fn every_prefix_is_a_rule() {
        LazyLock::force(&TRIE);
    }

    #[test]
    fn an_index_computation_is_one_spell_with_its_guard() {
        // s[(p - 1) % 256 + 1], p in slot 5, the key in slot 6, the table in slot 1.
        let mut spells = Spells::default();
        for o in [op(Arith::Sub, Slot(5), K(1), 6), op(Arith::Mod, Slot(6), K(256), 6), op(Arith::Add, Slot(6), K(1), 6)] {
            assert_eq!(spells.offer(&o), Offer::Held);
        }
        assert!(spells.offer_guard(&crate::generators::InArrayHeld::new(&[1, 6])));
        let [spell] = &spells.spells[..] else { panic!("{spells:?}") };
        assert_eq!(spell.rule(), "SUB_MASK_ADD_HELD");
        let (check, compute) = spell.windows();
        assert_eq!((check.name(), check.operands()), ("CheckSubMaskAddHeld", &[1, 5][..]));
        assert_eq!((compute.name(), compute.operands()), ("ComputeSubMaskAddHeld", &[5, 6][..]));
    }

    #[test]
    fn interleaved_chains_are_held_apart() {
        // A B C D: x = x + 1; y = y - 2; x = x % 256; y = y % 16, on slots 1 and 2.
        let mut spells = Spells::default();
        for o in [op(Arith::Add, Slot(1), K(1), 1), op(Arith::Sub, Slot(2), K(2), 2), op(Arith::Mod, Slot(1), K(256), 1), op(Arith::Mod, Slot(2), K(16), 2)] {
            assert_eq!(spells.offer(&o), Offer::Held, "{o:?}");
        }
        let rules: Vec<_> = spells.spells.iter().map(|s| s.rule()).collect();
        assert_eq!(rules, ["ADD_MASK", "SUB_MASK"]);
    }

    #[test]
    fn a_value_overwritten_unread_is_dropped() {
        let mut spells = Spells::default();
        assert_eq!(spells.offer(&op(Arith::Add, Slot(1), K(1), 3)), Offer::Held);
        assert_eq!(spells.offer(&op(Arith::Sub, Slot(2), K(1), 3)), Offer::Held);
        let [spell] = &spells.spells[..] else { panic!("{spells:?}") };
        assert_eq!((spell.rule(), spell.inputs.as_slice()), ("SUB_", &[2][..]));
    }

    #[test]
    fn dead_values_are_never_laid_out() {
        // A chain overwritten unread: t = x + 1; t = t % 256; then t = y - 2.
        let mut spells = Spells::default();
        for o in [op(Arith::Add, Slot(1), K(1), 3), op(Arith::Mod, Slot(3), K(256), 3), op(Arith::Sub, Slot(2), K(2), 3)] {
            assert_eq!(spells.offer(&o), Offer::Held, "{o:?}");
        }
        let [spell] = &spells.spells[..] else { panic!("{spells:?}") };
        assert_eq!((spell.rule(), spell.inputs.as_slice()), ("SUB_", &[2][..]));
        // Among live ones: x = x + 1 lives on, t = y + 2 doesn't, overwritten by t = z + 5.
        let mut spells = Spells::default();
        for o in [op(Arith::Add, Slot(1), K(1), 1), op(Arith::Add, Slot(2), K(2), 3), op(Arith::Add, Slot(4), K(5), 3)] {
            assert_eq!(spells.offer(&o), Offer::Held, "{o:?}");
        }
        let held: Vec<_> = spells.spells.iter().map(|s| (s.dest, s.inputs.clone())).collect();
        assert_eq!(held, [(1, vec![1]), (3, vec![4])]);
        // Read before it is overwritten: not dead, and laid out first.
        let mut spells = Spells::default();
        assert_eq!(spells.offer(&op(Arith::Add, Slot(1), K(1), 3)), Offer::Held);
        assert_eq!(spells.offer(&op(Arith::Add, Slot(3), K(1), 4)), Offer::Flush);
        assert_eq!(spells.spells.len(), 1);
        // Overwritten by what can't be held: dropped, nothing left to lay out.
        let mut spells = Spells::default();
        assert_eq!(spells.offer(&op(Arith::Add, Slot(1), K(1), 3)), Offer::Held);
        assert_eq!(spells.offer(&op(Arith::Mul, Slot(2), K(-2), 3)), Offer::Refused);
        assert!(spells.is_empty());
        // Overwritten by something else laid out, as a constant loaded into it; one reading it
        // keeps it.
        let mut spells = Spells::default();
        assert_eq!(spells.offer(&op(Arith::Add, Slot(1), K(1), 3)), Offer::Held);
        let mut kept = spells.clone();
        kept.drop_overwritten(&[3], &[3]);
        assert_eq!(kept.spells.len(), 1);
        spells.drop_overwritten(&[3], &[]);
        assert!(spells.is_empty());
    }

    #[test]
    fn what_lays_out_the_spells() {
        let mut spells = Spells::default();
        assert_eq!(spells.offer(&op(Arith::Add, Slot(1), K(1), 3)), Offer::Held);
        // Writing a slot a spell reads.
        assert_eq!(spells.clone().offer(&op(Arith::Add, Slot(4), K(1), 1)), Offer::Flush);
        // Reading a held value without joining: into another slot, or no rule going on.
        assert_eq!(spells.clone().offer(&op(Arith::Add, Slot(3), K(1), 4)), Offer::Flush);
        assert_eq!(spells.clone().offer(&op(Arith::Mul, Slot(3), K(-2), 3)), Offer::Flush);
        // A product that could be -0, with nothing held, is refused.
        assert_eq!(Spells::default().offer(&op(Arith::Mul, Slot(3), K(-2), 3)), Offer::Refused);
        // A guard on a key held is joined, ending its spell; on another, not.
        assert!(!spells.joins_guard(&crate::generators::InArray::new(&[2, 5])));
        assert!(spells.offer_guard(&crate::generators::InArray::new(&[2, 3])));
        assert_eq!(spells.offer(&op(Arith::Add, Slot(3), K(1), 3)), Offer::Flush);
    }

    #[test]
    fn a_pair_and_its_steps() {
        // (p + k + 1) % 256 into slot 3: p in slot 1, k in slot 2.
        let mut spells = Spells::default();
        for o in [op(Arith::Add, Slot(1), Slot(2), 3), op(Arith::Add, Slot(3), K(1), 3), op(Arith::Mod, Slot(3), K(256), 3)] {
            assert_eq!(spells.offer(&o), Offer::Held, "{o:?}");
        }
        assert_eq!(spells.spells[0].rule(), "RR_ADD_ADD_MASK");
        // n * 256 + t: the product's register stepped, then summed with another.
        let mut spells = Spells::default();
        for o in [op(Arith::Mul, Slot(1), K(256), 3), op(Arith::Add, Slot(3), Slot(2), 3)] {
            assert_eq!(spells.offer(&o), Offer::Held, "{o:?}");
        }
        let (check, compute) = spells.spells[0].windows();
        assert_eq!((spells.spells[0].rule(), check.operands(), compute.operands()), ("MUL_RR_ADD", &[1, 2][..], &[1, 2, 3][..]));
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
