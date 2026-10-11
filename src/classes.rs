//! Classes of the equal values a context's locations hold, with what is known of each class's
//! value. See Note [Value classes].

use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

// Note [Value classes]
// ~~~~~~~~~~~~~~~~~~~~
// A context knows things about values, not about the places holding them: a slot and an upvalue
// loaded from it hold one value, and what a guard on either finds is true of both. So the places
// a context knows of are partitioned into classes of equal values, and what is known is known of a
// class.
//
// The places are roots, the frame's slots and the running function's own upvalues, and fields: a
// labelled edge from a class to the class its field holds, as the closure a class's value is has
// its upvalues, or a value loaded from a table's array part has the table it was loaded from. A
// field reached from a class holds the same value whatever place the class is reached from, so a
// closure moved to another slot keeps what is known of its upvalues.
//
// A write to a place moves it to a class of its own, which nothing is known of, and leaves the
// rest of its old class as it was: facts follow values, and nothing else is falsified. A class no
// place reaches any more is forgotten, and so is one nothing is known of (no facts, no fields, and
// only one place holding it), as that is what a place no class names means. An upvalue captured
// while its slot is open is that slot, not a copy of its value: its field names the slot itself
// (`Target::Open`), so a write to the slot is one to the upvalue, until the slot is closed and the
// field holds the value it then had.
//
// The classes are kept in a canonical form, numbered in the order they are first reached from the
// roots in order and then along fields in label order, with nothing kept that tells nothing. Two
// contexts knowing the same equalities and facts are then equal and hash equal, as a version's key
// needs.
//
// A version relying on what one context knows accepts another (`accepts`) if the other knows at
// least as much: every two places equal in the first are equal in the other, every fact of a class
// in the first is implied by one of the other's class, and every field the first knows the other
// does. The join of two contexts (`join`) knows what both do: two places are equal in it if they
// are in both, and a class's facts are the joins of the two's.
//
// Each key of fact is a domain of its own, and so are the equalities: what is known in one can be
// forgotten without forgetting anything in another. Forgetting a fact leaves the classes as they
// are, and splitting a class leaves each part every fact the class had, as facts follow values.
// So a context can be lowered towards another in one domain alone (`lower_facts`,
// `lower_partition`), keeping only what the other knows there too.
//
// Where the other knows nothing of a place, the places reached from it along fields keep the
// equalities they have among themselves: a closure whose upvalue is itself (a recursive local
// function) would otherwise split into endlessly many places.

/// A place the frame names directly.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Root {
    Slot(u16),
    Upvalue(u8),
}

/// The field a class's value has, which another class's value is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Label {
    /// Upvalue n of the closure it is.
    Upvalue(u8),
    /// The table whose array part it was loaded from.
    ElementOf,
}

/// A place: a root, or a field reached from one along `path`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Loc<'a> {
    pub root: Root,
    pub path: &'a [Label],
}

impl Loc<'static> {
    pub fn root(root: Root) -> Self {
        Loc { root, path: &[] }
    }
}

/// What can be known of a class's value. A class has at most one fact of a key.
pub trait ClassFact: Clone + Eq + Hash + Debug {
    type Key: Ord + Copy + Eq + Hash + Debug;
    fn key(&self) -> Self::Key;
    /// What is known of a value known either as `self` or as `other`, of the same key, if anything.
    fn join(&self, other: &Self) -> Option<Self>;
    /// Whether a value known as `self` is known as `weaker`, of the same key, too.
    fn implies(&self, weaker: &Self) -> bool;
}

/// What a field holds: a class, or an open slot's value whatever it is now.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Target {
    Class(u32),
    Open(u16),
}

/// What `above` has at the places a class of a context is, as `Classes::resolve` names a place: a
/// class there, a root it knows nothing of, or a field one of its classes doesn't know of. See
/// `Classes::pairs`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Side {
    Class(u32),
    Root(Root),
    Field(u32, Label),
}

/// What a context has at the places of a pair, named as `Side` names `above`'s. See
/// `Classes::pairs`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Mine {
    Class(u32),
    Root(Root),
    Field(u32, Label),
}

/// What a field of a pair holds: a pair, or an open slot.
#[derive(Debug, Clone, Copy)]
enum PairTarget {
    Pair(usize),
    Open(u16),
}

/// A context's classes paired with what another has at the same places, reached from the roots
/// and along the context's fields. See `Classes::pairs`.
struct Pairs {
    pairs: Vec<(Mine, Side)>,
    roots: Vec<(Root, usize)>,
    fields: Vec<(usize, Label, PairTarget)>,
}

/// The classes of a context's places. See Note [Value classes].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Classes<F> {
    /// Each root a class holds, by root.
    roots: Vec<(Root, u32)>,
    /// Each field a class's value has, by class and label.
    fields: Vec<(u32, Label, Target)>,
    /// Each class's facts, by class, each class's by key.
    facts: Vec<(u32, Vec<F>)>,
    /// How many classes there are, numbered from 0.
    classes: u32,
}

impl<F> Default for Classes<F> {
    fn default() -> Self {
        Classes { roots: Vec::new(), fields: Vec::new(), facts: Vec::new(), classes: 0 }
    }
}

impl<F: ClassFact> Classes<F> {
    fn root_class(&self, root: Root) -> Option<u32> {
        self.roots.binary_search_by_key(&root, |&(r, _)| r).ok().map(|i| self.roots[i].1)
    }

    fn field(&self, class: u32, label: Label) -> Option<Target> {
        self.fields.iter().find(|&&(c, l, _)| c == class && l == label).map(|&(_, _, t)| t)
    }

    fn target_class(&self, target: Target) -> Option<u32> {
        match target {
            Target::Class(class) => Some(class),
            Target::Open(slot) => self.root_class(Root::Slot(slot)),
        }
    }

    /// The class `loc` holds, if anything is known of it.
    fn find(&self, loc: Loc) -> Option<u32> {
        let mut class = self.root_class(loc.root)?;
        for &label in loc.path {
            class = self.target_class(self.field(class, label)?)?;
        }
        Some(class)
    }

    fn new_class(&mut self) -> u32 {
        self.classes += 1;
        self.classes - 1
    }

    fn bind(&mut self, root: Root, class: u32) {
        match self.roots.binary_search_by_key(&root, |&(r, _)| r) {
            Ok(i) => self.roots[i].1 = class,
            Err(i) => self.roots.insert(i, (root, class)),
        }
    }

    fn set_field(&mut self, class: u32, label: Label, target: Target) {
        match self.fields.iter().position(|&(c, l, _)| c == class && l == label) {
            Some(i) => self.fields[i].2 = target,
            None => self.fields.push((class, label, target)),
        }
    }

    /// The class `loc` holds, made if nothing was known of it.
    fn ensure(&mut self, loc: Loc) -> u32 {
        let mut class = match self.root_class(loc.root) {
            Some(class) => class,
            None => {
                let class = self.new_class();
                self.bind(loc.root, class);
                class
            },
        };
        for &label in loc.path {
            class = match self.field(class, label) {
                Some(Target::Class(next)) => next,
                Some(Target::Open(slot)) => self.ensure(Loc::root(Root::Slot(slot))),
                None => {
                    let next = self.new_class();
                    self.set_field(class, label, Target::Class(next));
                    next
                },
            };
        }
        class
    }

    /// How far `loc` resolves: the last class or unknown root it reaches, and the labels past it.
    fn resolve<'a>(&self, loc: Loc<'a>) -> (Result<u32, Root>, &'a [Label]) {
        let Some(mut class) = self.root_class(loc.root) else { return (Err(loc.root), loc.path) };
        for (i, &label) in loc.path.iter().enumerate() {
            match self.field(class, label) {
                Some(Target::Class(next)) => class = next,
                Some(Target::Open(slot)) => match self.root_class(Root::Slot(slot)) {
                    Some(next) => class = next,
                    None => return (Err(Root::Slot(slot)), &loc.path[i + 1..]),
                },
                None => return (Ok(class), &loc.path[i..]),
            }
        }
        (Ok(class), &[])
    }

    /// Whether `a` and `b` hold the same value: they are one place, or reach one.
    pub fn same(&self, a: Loc, b: Loc) -> bool {
        self.resolve(a) == self.resolve(b)
    }

    /// What is known of the value `loc` holds.
    pub fn facts(&self, loc: Loc) -> &[F] {
        self.find(loc)
            .and_then(|class| self.facts.iter().find(|(c, _)| *c == class))
            .map_or(&[], |(_, facts)| facts.as_slice())
    }

    /// The fact of `key` known of the value `loc` holds.
    pub fn fact(&self, loc: Loc, key: F::Key) -> Option<&F> {
        self.facts(loc).iter().find(|fact| fact.key() == key)
    }

    /// The roots holding the value `loc` holds, in order.
    pub fn members(&self, loc: Loc) -> Vec<Root> {
        match self.find(loc) {
            Some(class) => self.roots.iter().filter(|&&(_, c)| c == class).map(|&(r, _)| r).collect(),
            None => vec![loc.root].into_iter().filter(|_| loc.path.is_empty()).collect(),
        }
    }

    /// `dst` holds the value `src` does.
    pub fn assign(&mut self, dst: Root, src: Loc) {
        let class = self.ensure(src);
        self.bind(dst, class);
        self.normalize();
    }

    /// `dst` holds a value nothing is known of.
    pub fn write(&mut self, dst: Root) {
        self.roots.retain(|&(r, _)| r != dst);
        self.normalize();
    }

    /// The value `loc` holds is known as `fact`, in place of what was known of its key.
    pub fn learn(&mut self, loc: Loc, fact: F) {
        let class = self.ensure(loc);
        let key = fact.key();
        match self.facts.iter_mut().find(|(c, _)| *c == class) {
            Some((_, facts)) => match facts.binary_search_by_key(&key, |f| f.key()) {
                Ok(i) => facts[i] = fact,
                Err(i) => facts.insert(i, fact),
            },
            None => self.facts.push((class, vec![fact])),
        }
        self.normalize();
    }

    /// Nothing is known of `key` of the value `loc` holds.
    pub fn forget(&mut self, loc: Loc, key: F::Key) {
        if let Some(class) = self.find(loc) {
            for (c, facts) in &mut self.facts {
                if *c == class {
                    facts.retain(|fact| fact.key() != key);
                }
            }
            self.normalize();
        }
    }

    /// The value `from` holds has field `label`, the value `to` holds.
    pub fn link(&mut self, from: Loc, label: Label, to: Loc) {
        let target = self.ensure(to);
        let class = self.ensure(from);
        self.set_field(class, label, Target::Class(target));
        self.normalize();
    }

    /// The value `from` holds has field `label`, which is slot `slot` while the slot is open.
    pub fn alias(&mut self, from: Loc, label: Label, slot: u16) {
        let class = self.ensure(from);
        self.set_field(class, label, Target::Open(slot));
        self.normalize();
    }

    /// The slots from `from` on are closed: a field that was one holds the value it had.
    pub fn close(&mut self, from: u16) {
        let open: Vec<(usize, u16)> = self.fields.iter().enumerate()
            .filter_map(|(i, &(_, _, target))| match target {
                Target::Open(slot) if slot >= from => Some((i, slot)),
                _ => None,
            })
            .collect();
        for (i, slot) in open {
            let class = self.ensure(Loc::root(Root::Slot(slot)));
            self.fields[i].2 = Target::Class(class);
        }
        self.normalize();
    }

    /// Keep only the facts `keep` says to.
    pub fn retain_facts(&mut self, mut keep: impl FnMut(&F) -> bool) {
        for (_, facts) in &mut self.facts {
            facts.retain(|fact| keep(fact));
        }
        self.normalize();
    }

    /// Keep only the fields `keep` says to.
    pub fn retain_fields(&mut self, mut keep: impl FnMut(Label, Target) -> bool) {
        self.fields.retain(|&(_, label, target)| keep(label, target));
        self.normalize();
    }

    /// The classes another frame sees, its root `r` holding what `loc` does here for each
    /// `(r, loc)` of `map`: its other roots hold values nothing is known of, and a field open here
    /// holds the value it now has, as its slot isn't one of the other frame's.
    pub fn view(&self, map: &[(Root, Loc)]) -> Self {
        let mut seen = self.clone();
        let open: Vec<u16> = seen.fields.iter().filter_map(|&(_, _, t)| match t { Target::Open(slot) => Some(slot), _ => None }).collect();
        for slot in open {
            seen.close_one(slot);
        }
        let mut roots: Vec<(Root, u32)> = map.iter().filter_map(|&(root, loc)| seen.find(loc).map(|class| (root, class))).collect();
        roots.sort();
        roots.dedup_by_key(|&mut (root, _)| root);
        let mut view = Classes { roots, fields: seen.fields, facts: seen.facts, classes: seen.classes };
        view.normalize();
        view
    }

    fn close_one(&mut self, slot: u16) {
        let class = self.ensure(Loc::root(Root::Slot(slot)));
        for field in &mut self.fields {
            if field.2 == Target::Open(slot) {
                field.2 = Target::Class(class);
            }
        }
    }

    /// Each root `r` of `map`'s `(r, loc)` holds what `loc` holds in `other`, and nothing else
    /// changes: roots `other` holds equal are equal, and a root here holds no value one of them
    /// does unless `other` says so too.
    pub fn overlay(&mut self, other: &Classes<F>, map: &[(Root, Loc)]) {
        let theirs = other.view(&map.iter().enumerate().map(|(i, &(_, loc))| (Root::Slot(i as u16), loc)).collect::<Vec<_>>());
        let taken: Vec<Root> = map.iter().map(|&(root, _)| root).collect();
        self.roots.retain(|(root, _)| !taken.contains(root));
        let offset = self.classes;
        for &(root, class) in &theirs.roots {
            let Root::Slot(i) = root else { unreachable!() };
            self.bind(map[i as usize].0, class + offset);
        }
        self.fields.extend(theirs.fields.iter().map(|&(c, l, t)| (c + offset, l, match t {
            Target::Class(t) => Target::Class(t + offset),
            open => open,
        })));
        self.facts.extend(theirs.facts.iter().map(|(c, f)| (c + offset, f.clone())));
        self.classes += theirs.classes;
        self.normalize();
    }

    /// What both `self` and `other` know.
    pub fn join(&self, other: &Self) -> Self {
        let mut joined = Classes::default();
        let mut pairs: HashMap<(u32, u32), u32> = HashMap::new();
        let mut work: Vec<(u32, u32, u32)> = Vec::new();
        let mut pair = |joined: &mut Classes<F>, work: &mut Vec<(u32, u32, u32)>, a: u32, b: u32| {
            *pairs.entry((a, b)).or_insert_with(|| {
                let class = joined.new_class();
                work.push((a, b, class));
                class
            })
        };
        for &(root, a) in &self.roots {
            if let Some(b) = other.root_class(root) {
                let class = pair(&mut joined, &mut work, a, b);
                joined.bind(root, class);
            }
        }
        while let Some((a, b, class)) = work.pop() {
            let mine = self.facts.iter().find(|(c, _)| *c == a).map_or(&[][..], |(_, f)| f.as_slice());
            let theirs = other.facts.iter().find(|(c, _)| *c == b).map_or(&[][..], |(_, f)| f.as_slice());
            let facts: Vec<F> = mine.iter()
                .filter_map(|fact| theirs.iter().find(|t| t.key() == fact.key()).and_then(|t| fact.join(t)))
                .collect();
            if !facts.is_empty() {
                joined.facts.push((class, facts));
            }
            for &(_, label, mine) in self.fields.iter().filter(|&&(c, _, _)| c == a) {
                let Some(theirs) = other.field(b, label) else { continue };
                let target = match (mine, theirs) {
                    (Target::Class(x), Target::Class(y)) => Target::Class(pair(&mut joined, &mut work, x, y)),
                    (Target::Open(x), Target::Open(y)) if x == y => Target::Open(x),
                    _ => continue,
                };
                joined.fields.push((class, label, target));
            }
        }
        joined.normalize();
        joined
    }

    /// Whether code relying on what `self` knows can run in `other`: `other` knows at least as
    /// much.
    pub fn accepts(&self, other: &Self) -> bool {
        let mut mapped: HashMap<u32, u32> = HashMap::new();
        let mut work: Vec<(u32, u32)> = Vec::new();
        let mut map = |work: &mut Vec<(u32, u32)>, mine: u32, theirs: u32| match mapped.get(&mine) {
            Some(&known) => known == theirs,
            None => {
                mapped.insert(mine, theirs);
                work.push((mine, theirs));
                true
            },
        };
        for &(root, mine) in &self.roots {
            let Some(theirs) = other.root_class(root) else { return false };
            if !map(&mut work, mine, theirs) {
                return false;
            }
        }
        while let Some((mine, theirs)) = work.pop() {
            let known = other.facts.iter().find(|(c, _)| *c == theirs).map_or(&[][..], |(_, f)| f.as_slice());
            for (_, facts) in self.facts.iter().filter(|(c, _)| *c == mine) {
                for fact in facts {
                    if !known.iter().any(|k| k.key() == fact.key() && k.implies(fact)) {
                        return false;
                    }
                }
            }
            for &(_, label, target) in self.fields.iter().filter(|&&(c, _, _)| c == mine) {
                match (target, other.field(theirs, label)) {
                    (Target::Class(x), Some(Target::Class(y))) => {
                        if !map(&mut work, x, y) {
                            return false;
                        }
                    },
                    (Target::Open(x), Some(Target::Open(y))) if x == y => {},
                    _ => return false,
                }
            }
        }
        true
    }

    /// Each class paired with what `above` has at each place it is: a class reaching places
    /// `above` has in two classes is two pairs. A field `above` has open at the same place is
    /// kept open; one open only here holds the slot's value. A field only `above` knows of is a
    /// pair too, so places equal here and in `above` through it stay equal. See Note [Value
    /// classes].
    fn pairs(&self, above: &Self) -> Pairs {
        let mut index: HashMap<(Mine, Side), usize> = HashMap::new();
        let mut pairs: Vec<(Mine, Side)> = Vec::new();
        let mut intern = |pairs: &mut Vec<(Mine, Side)>, pair: (Mine, Side)| *index.entry(pair).or_insert_with(|| {
            pairs.push(pair);
            pairs.len() - 1
        });
        let mut roots = Vec::new();
        for &(root, class) in &self.roots {
            let side = above.root_class(root).map_or(Side::Root(root), Side::Class);
            roots.push((root, intern(&mut pairs, (Mine::Class(class), side))));
        }
        let mut fields = Vec::new();
        let mut i = 0;
        while i < pairs.len() {
            let (Mine::Class(class), side) = pairs[i] else {
                i += 1;
                continue;
            };
            if let Side::Class(a) = side {
                for &(_, label, theirs) in above.fields.iter().filter(|&&(c, _, _)| c == a) {
                    if self.field(class, label).is_none() && let Some(t) = above.target_class(theirs) {
                        let pair = intern(&mut pairs, (Mine::Field(class, label), Side::Class(t)));
                        fields.push((i, label, PairTarget::Pair(pair)));
                    }
                }
            }
            for &(_, label, target) in self.fields.iter().filter(|&&(c, _, _)| c == class) {
                let theirs = match side {
                    Side::Class(a) => above.field(a, label),
                    _ => None,
                };
                // Past a place `above` knows nothing of, what is reached keeps its equalities.
                let beyond = |above_target: Option<Target>| match (side, above_target) {
                    (Side::Class(a), Some(Target::Open(k))) => above.root_class(Root::Slot(k)).map_or(Side::Root(Root::Slot(k)), Side::Class),
                    (Side::Class(_), Some(Target::Class(t))) => Side::Class(t),
                    (Side::Class(a), None) => Side::Field(a, label),
                    (unknown, _) => unknown,
                };
                let paired = match (target, theirs) {
                    (Target::Open(k), Some(Target::Open(j))) if k == j => PairTarget::Open(k),
                    (Target::Open(k), theirs) => {
                        let held = self.root_class(Root::Slot(k)).map_or(Mine::Root(Root::Slot(k)), Mine::Class);
                        PairTarget::Pair(intern(&mut pairs, (held, beyond(theirs))))
                    },
                    (Target::Class(t), theirs) => PairTarget::Pair(intern(&mut pairs, (Mine::Class(t), beyond(theirs)))),
                };
                fields.push((i, label, paired));
            }
            i += 1;
        }
        Pairs { pairs, roots, fields }
    }

    /// Keep each fact of `key` only where `above` has the same fact at every place its class
    /// is, leaving every other fact and the classes as they are. See Note [Value classes].
    pub fn lower_facts(&mut self, key: F::Key, above: &Self) {
        let pairs = self.pairs(above);
        let mut keep = vec![true; self.classes as usize];
        for &(mine, side) in &pairs.pairs {
            let Mine::Class(class) = mine else { continue };
            let Some(mine) = self.facts.iter().find(|(c, _)| *c == class).and_then(|(_, facts)| facts.iter().find(|f| f.key() == key)) else { continue };
            let theirs = match side {
                Side::Class(a) => above.facts.iter().find(|(c, _)| *c == a).and_then(|(_, facts)| facts.iter().find(|f| f.key() == key)),
                _ => None,
            };
            if theirs != Some(mine) {
                keep[class as usize] = false;
            }
        }
        for (class, facts) in &mut self.facts {
            if !keep[*class as usize] {
                facts.retain(|fact| fact.key() != key);
            }
        }
        self.normalize();
    }

    /// Split the classes so that two places are equal only if they are in `above` too, each part
    /// keeping every fact its class had; a field open only here holds its slot's value. See Note
    /// [Value classes].
    pub fn lower_partition(&mut self, above: &Self) {
        let pairs = self.pairs(above);
        let mut lowered = Classes {
            roots: pairs.roots.iter().map(|&(root, pair)| (root, pair as u32)).collect(),
            fields: pairs.fields.iter().map(|&(pair, label, target)| (pair as u32, label, match target {
                PairTarget::Pair(t) => Target::Class(t as u32),
                PairTarget::Open(k) => Target::Open(k),
            })).collect(),
            facts: Vec::new(),
            classes: pairs.pairs.len() as u32,
        };
        for (pair, &(mine, _)) in pairs.pairs.iter().enumerate() {
            let Mine::Class(class) = mine else { continue };
            if let Some((_, facts)) = self.facts.iter().find(|(c, _)| *c == class) {
                lowered.facts.push((pair as u32, facts.clone()));
            }
        }
        lowered.normalize();
        *self = lowered;
    }

    /// Forget what tells nothing and what nothing reaches, and number the classes in the order
    /// they are reached. See Note [Value classes].
    fn normalize(&mut self) {
        loop {
            // What no root reaches, along fields.
            let mut reached = vec![false; self.classes as usize];
            let mut work: Vec<u32> = self.roots.iter().map(|&(_, class)| class).collect();
            while let Some(class) = work.pop() {
                if !std::mem::replace(&mut reached[class as usize], true) {
                    work.extend(self.fields.iter().filter_map(|&(c, _, t)| match t {
                        Target::Class(t) if c == class => Some(t),
                        _ => None,
                    }));
                }
            }
            let fields_before = self.fields.len();
            self.fields.retain(|&(class, _, _)| reached[class as usize]);
            self.facts.retain(|&(class, _)| reached[class as usize]);
            // What tells nothing.
            let mut held = vec![0u32; self.classes as usize];
            let mut has_fields = vec![false; self.classes as usize];
            for &(_, class) in &self.roots {
                held[class as usize] += 1;
            }
            for &(class, _, target) in &self.fields {
                has_fields[class as usize] = true;
                if let Target::Class(t) = target {
                    held[t as usize] += 1;
                }
            }
            let mut known = vec![false; self.classes as usize];
            for (class, facts) in &self.facts {
                known[*class as usize] |= !facts.is_empty();
            }
            let empty = |class: u32| !known[class as usize] && !has_fields[class as usize] && held[class as usize] <= 1;
            let before = (self.roots.len(), self.fields.len());
            self.roots.retain(|&(_, class)| !empty(class));
            self.fields.retain(|&(_, _, target)| !matches!(target, Target::Class(t) if empty(t)));
            if (self.roots.len(), self.fields.len()) == before && self.fields.len() == fields_before {
                break;
            }
        }
        let mut number: Vec<Option<u32>> = vec![None; self.classes as usize];
        let mut order: Vec<u32> = Vec::new();
        let mut reach = |class: u32, order: &mut Vec<u32>| {
            if number[class as usize].is_none() {
                number[class as usize] = Some(order.len() as u32);
                order.push(class);
            }
        };
        for &(_, class) in &self.roots {
            reach(class, &mut order);
        }
        let mut fields = std::mem::take(&mut self.fields);
        fields.sort_by_key(|&(class, label, _)| (class, label));
        let mut i = 0;
        while i < order.len() {
            let class = order[i];
            for &(_, _, target) in fields.iter().filter(|&&(c, _, _)| c == class) {
                if let Target::Class(t) = target {
                    reach(t, &mut order);
                }
            }
            i += 1;
        }
        let renumber = |class: u32| number[class as usize];
        for root in &mut self.roots {
            root.1 = renumber(root.1).unwrap();
        }
        self.fields = fields.into_iter()
            .filter_map(|(class, label, target)| Some((renumber(class)?, label, match target {
                Target::Class(t) => Target::Class(renumber(t).unwrap()),
                open => open,
            })))
            .collect();
        self.fields.sort();
        self.facts = std::mem::take(&mut self.facts).into_iter()
            .filter(|(_, facts)| !facts.is_empty())
            .filter_map(|(class, mut facts)| {
                facts.sort_by_key(|f| f.key());
                Some((renumber(class)?, facts))
            })
            .collect();
        self.facts.sort_by_key(|&(class, _)| class);
        self.classes = order.len() as u32;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::Hasher;

    /// A type lattice (`Int`, `Float` below `Number`), and a constant, which joins only with
    /// itself.
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    enum Fact {
        Type(Ty),
        Constant(i32),
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    enum Ty {
        Int,
        Float,
        Number,
    }

    impl ClassFact for Fact {
        type Key = u8;
        fn key(&self) -> u8 {
            match self {
                Fact::Type(_) => 0,
                Fact::Constant(_) => 1,
            }
        }
        fn join(&self, other: &Self) -> Option<Self> {
            match (self, other) {
                (Fact::Type(a), Fact::Type(b)) => Some(Fact::Type(if a == b { *a } else { Ty::Number })),
                (Fact::Constant(a), Fact::Constant(b)) => (a == b).then_some(Fact::Constant(*a)),
                _ => None,
            }
        }
        fn implies(&self, weaker: &Self) -> bool {
            match (self, weaker) {
                (Fact::Type(a), Fact::Type(b)) => a == b || *b == Ty::Number,
                (a, b) => a == b,
            }
        }
    }

    type C = Classes<Fact>;

    fn slot(i: u16) -> Loc<'static> {
        Loc::root(Root::Slot(i))
    }

    fn up(j: u8) -> Loc<'static> {
        Loc::root(Root::Upvalue(j))
    }

    fn hash(c: &C) -> u64 {
        let mut h = DefaultHasher::new();
        c.hash(&mut h);
        h.finish()
    }

    /// xorshift, so the random tests are reproducible.
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    const ROOTS: [Root; 6] = [Root::Slot(0), Root::Slot(1), Root::Slot(2), Root::Slot(3), Root::Upvalue(0), Root::Upvalue(1)];
    const LABELS: [Label; 3] = [Label::Upvalue(0), Label::Upvalue(1), Label::ElementOf];
    const FACTS: [Fact; 5] = [Fact::Type(Ty::Int), Fact::Type(Ty::Float), Fact::Type(Ty::Number), Fact::Constant(1), Fact::Constant(2)];

    /// What a field of a value in the reference holds.
    #[derive(Debug, Clone, Copy, PartialEq)]
    enum RefField {
        Value(u32),
        Open(u16),
    }

    /// The reference: every root holds a value, numbered as written; facts and fields are of
    /// values. Two places are the same if they hold the same value.
    #[derive(Debug, Clone, Default)]
    struct Reference {
        values: HashMap<Root, u32>,
        facts: HashMap<u32, Vec<Fact>>,
        fields: HashMap<(u32, Label), RefField>,
        next: u32,
    }

    impl Reference {
        fn fresh(&mut self) -> u32 {
            self.next += 1;
            self.next
        }
        fn value(&self, root: Root, path: &[Label]) -> Option<u32> {
            let mut value = *self.values.get(&root)?;
            for &label in path {
                value = match *self.fields.get(&(value, label))? {
                    RefField::Value(v) => v,
                    RefField::Open(slot) => *self.values.get(&Root::Slot(slot))?,
                };
            }
            Some(value)
        }
        /// How far a place resolves: the last value or unknown root it reaches, and the labels
        /// past it. Two places resolving alike are one place.
        fn resolve(&self, root: Root, path: &[Label]) -> (Result<u32, Root>, Vec<Label>) {
            let Some(&first) = self.values.get(&root) else { return (Err(root), path.to_vec()) };
            let mut value = first;
            for (i, &label) in path.iter().enumerate() {
                match self.fields.get(&(value, label)) {
                    Some(RefField::Value(v)) => value = *v,
                    Some(RefField::Open(slot)) => match self.values.get(&Root::Slot(*slot)) {
                        Some(&v) => value = v,
                        None => return (Err(Root::Slot(*slot)), path[i + 1..].to_vec()),
                    },
                    None => return (Ok(value), path[i..].to_vec()),
                }
            }
            (Ok(value), vec![])
        }
        fn ensure(&mut self, root: Root, path: &[Label]) -> u32 {
            let mut value = match self.values.get(&root) {
                Some(&v) => v,
                None => {
                    let v = self.fresh();
                    self.values.insert(root, v);
                    v
                },
            };
            for &label in path {
                value = match self.fields.get(&(value, label)).copied() {
                    Some(RefField::Value(v)) => v,
                    Some(RefField::Open(slot)) => self.ensure(Root::Slot(slot), &[]),
                    None => {
                        let v = self.fresh();
                        self.fields.insert((value, label), RefField::Value(v));
                        v
                    },
                };
            }
            value
        }
        fn learn(&mut self, root: Root, path: &[Label], fact: Fact) {
            let v = self.ensure(root, path);
            let facts = self.facts.entry(v).or_default();
            facts.retain(|f| f.key() != fact.key());
            facts.push(fact);
        }
        fn facts_of(&self, root: Root, path: &[Label]) -> Vec<Fact> {
            let mut facts = self.value(root, path).and_then(|v| self.facts.get(&v)).cloned().unwrap_or_default();
            facts.sort_by_key(|f| f.key());
            facts
        }
    }

    /// One random operation, on both.
    fn step(rng: &mut Rng, c: &mut C, r: &mut Reference) {
        let root = ROOTS[rng.below(ROOTS.len() as u64) as usize];
        let other = ROOTS[rng.below(ROOTS.len() as u64) as usize];
        let label = LABELS[rng.below(LABELS.len() as u64) as usize];
        let path: &[Label] = if rng.below(3) == 0 { std::slice::from_ref(&LABELS[rng.below(LABELS.len() as u64) as usize]) } else { &[] };
        match rng.below(7) {
            0 | 1 => {
                let v = r.ensure(other, path);
                r.values.insert(root, v);
                c.assign(root, Loc { root: other, path });
            },
            2 => {
                r.values.remove(&root);
                c.write(root);
            },
            3 | 4 => {
                let fact = FACTS[rng.below(FACTS.len() as u64) as usize].clone();
                r.learn(root, path, fact.clone());
                c.learn(Loc { root, path }, fact);
            },
            5 => {
                if rng.below(2) == 0 {
                    let to = r.ensure(other, &[]);
                    let from = r.ensure(root, &[]);
                    r.fields.insert((from, label), RefField::Value(to));
                    c.link(Loc::root(root), label, Loc::root(other));
                } else {
                    let s = rng.below(4) as u16;
                    let from = r.ensure(root, &[]);
                    r.fields.insert((from, label), RefField::Open(s));
                    c.alias(Loc::root(root), label, s);
                }
            },
            _ => {
                let from = rng.below(4) as u16;
                let open: Vec<((u32, Label), u16)> = r.fields.iter().filter_map(|(&k, &f)| match f {
                    RefField::Open(s) if s >= from => Some((k, s)),
                    _ => None,
                }).collect();
                for (k, s) in open {
                    let v = r.ensure(Root::Slot(s), &[]);
                    r.fields.insert(k, RefField::Value(v));
                }
                c.close(from);
            },
        }
    }

    /// The places checked: each root, and each field one label from it.
    fn places() -> Vec<(Root, Vec<Label>)> {
        ROOTS.iter().flat_map(|&root| std::iter::once((root, vec![])).chain(LABELS.iter().map(move |&l| (root, vec![l])))).collect()
    }

    /// The classes agree with the reference on every equality and fact among the places checked.
    fn agree(c: &C, r: &Reference) {
        let places = places();
        for (root, path) in &places {
            let loc = Loc { root: *root, path };
            let mut facts = c.facts(loc).to_vec();
            facts.sort_by_key(|f| f.key());
            assert_eq!(facts, r.facts_of(*root, path), "facts of {root:?} {path:?} in {c:?}");
            for (other, other_path) in &places {
                let theirs = Loc { root: *other, path: other_path };
                let expected = r.resolve(*root, path) == r.resolve(*other, other_path);
                assert_eq!(c.same(loc, theirs), expected, "{root:?} {path:?} and {other:?} {other_path:?} in {c:?} against {r:?}");
            }
        }
    }

    fn random(rng: &mut Rng, steps: usize) -> (C, Reference) {
        let (mut c, mut r) = (C::default(), Reference::default());
        for _ in 0..steps {
            step(rng, &mut c, &mut r);
        }
        (c, r)
    }

    #[test]
    fn classes_agree_with_values() {
        let mut rng = Rng(0x9e3779b97f4a7c15);
        for _ in 0..500 {
            let (mut c, mut r) = (C::default(), Reference::default());
            for _ in 0..40 {
                step(&mut rng, &mut c, &mut r);
                agree(&c, &r);
            }
        }
    }

    /// The same values, equalities, facts and fields, built in another order.
    fn rebuild(rng: &mut Rng, r: &Reference) -> C {
        let mut c = C::default();
        let mut groups: HashMap<u32, Vec<Root>> = HashMap::new();
        for (&root, &v) in &r.values {
            groups.entry(v).or_default().push(root);
        }
        let mut groups: Vec<(u32, Vec<Root>)> = groups.into_iter().collect();
        groups.sort_by_key(|(v, _)| *v);
        for i in (1..groups.len()).rev() {
            groups.swap(i, rng.below(i as u64 + 1) as usize);
        }
        // Each value's place to name it by: a root, or a field of a value with one.
        let mut named: HashMap<u32, (Root, Vec<Label>)> = HashMap::new();
        for (v, roots) in &mut groups {
            for i in (1..roots.len()).rev() {
                roots.swap(i, rng.below(i as u64 + 1) as usize);
            }
            for &other in &roots[1..] {
                c.assign(other, Loc::root(roots[0]));
            }
            named.insert(*v, (roots[0], vec![]));
        }
        let mut work: Vec<u32> = groups.iter().map(|(v, _)| *v).collect();
        let mut i = 0;
        while i < work.len() {
            let v = work[i];
            let (root, path) = named[&v].clone();
            let mut fields: Vec<(Label, RefField)> = r.fields.iter().filter(|((from, _), _)| *from == v).map(|((_, l), f)| (*l, *f)).collect();
            fields.sort_by_key(|(l, _)| *l);
            for (label, field) in fields {
                match field {
                    RefField::Open(s) => c.alias(Loc { root, path: &path }, label, s),
                    RefField::Value(t) => match named.get(&t).cloned() {
                        Some((troot, tpath)) => c.link(Loc { root, path: &path }, label, Loc { root: troot, path: &tpath }),
                        None => {
                            let mut tpath = path.clone();
                            tpath.push(label);
                            named.insert(t, (root, tpath));
                            work.push(t);
                        },
                    },
                }
            }
            i += 1;
        }
        for (v, (root, path)) in &named {
            for fact in r.facts.get(v).into_iter().flatten() {
                c.learn(Loc { root: *root, path }, fact.clone());
            }
        }
        c
    }

    #[test]
    fn equal_knowledge_is_equal_and_hashes_equal() {
        let mut rng = Rng(0x2545f4914f6cdd1d);
        for _ in 0..500 {
            let (c, r) = random(&mut rng, 30);
            let rebuilt = rebuild(&mut rng, &r);
            agree(&rebuilt, &r);
            assert_eq!(c, rebuilt, "against {r:?}");
            assert_eq!(hash(&c), hash(&rebuilt));
        }
    }

    #[test]
    fn writing_every_place_forgets_everything() {
        let mut rng = Rng(77);
        for _ in 0..200 {
            let (mut c, _) = random(&mut rng, 30);
            for root in ROOTS {
                c.write(root);
            }
            assert_eq!(c, C::default());
        }
    }

    #[test]
    fn facts_follow_values_not_places() {
        let mut c = C::default();
        c.assign(Root::Upvalue(0), slot(1));
        c.learn(slot(1), Fact::Type(Ty::Int));
        assert_eq!(c.fact(up(0), 0), Some(&Fact::Type(Ty::Int)), "what a guard on a slot finds, its upvalue learns");
        c.write(Root::Slot(1));
        assert_eq!(c.fact(up(0), 0), Some(&Fact::Type(Ty::Int)), "overwriting the slot keeps the upvalue's value's facts");
        assert_eq!(c.fact(slot(1), 0), None);
        assert_eq!(c.members(up(0)), vec![Root::Upvalue(0)]);
    }

    #[test]
    fn a_closures_upvalues_move_with_it() {
        let mut c = C::default();
        let field = [Label::Upvalue(0)];
        c.learn(Loc { root: Root::Slot(0), path: &field }, Fact::Type(Ty::Int));
        c.assign(Root::Slot(3), slot(0));
        c.write(Root::Slot(0));
        assert_eq!(c.fact(Loc { root: Root::Slot(3), path: &field }, 0), Some(&Fact::Type(Ty::Int)));
    }

    #[test]
    fn an_open_capture_is_its_slot_until_closed() {
        let mut c = C::default();
        let field = [Label::Upvalue(0)];
        let captured = Loc { root: Root::Slot(0), path: &field };
        c.learn(slot(2), Fact::Type(Ty::Int));
        c.alias(slot(0), Label::Upvalue(0), 2);
        assert_eq!(c.fact(captured, 0), Some(&Fact::Type(Ty::Int)));
        c.learn(slot(2), Fact::Type(Ty::Float));
        assert_eq!(c.fact(captured, 0), Some(&Fact::Type(Ty::Float)), "a write to the open slot is one to the upvalue");
        c.close(2);
        c.write(Root::Slot(2));
        assert_eq!(c.fact(captured, 0), Some(&Fact::Type(Ty::Float)), "once closed, the upvalue keeps the value it had");
        assert!(!c.same(captured, slot(2)));
    }

    #[test]
    fn joins_keep_what_both_know() {
        let mut rng = Rng(0xdeadbeef);
        for _ in 0..1000 {
            let (a, ra) = random(&mut rng, 25);
            let (b, rb) = random(&mut rng, 25);
            let j = a.join(&b);
            assert!(j.accepts(&a), "{j:?} doesn't accept {a:?}");
            assert!(j.accepts(&b), "{j:?} doesn't accept {b:?}");
            assert_eq!(j, b.join(&a));
            assert_eq!(a.join(&a), a);
            for root in ROOTS {
                for other in ROOTS {
                    let both = |r: &Reference| matches!((r.value(root, &[]), r.value(other, &[])), (Some(x), Some(y)) if x == y);
                    if both(&ra) && both(&rb) {
                        assert!(j.same(Loc::root(root), Loc::root(other)), "{root:?} and {other:?} are equal in both");
                    }
                }
                for fact in a.facts(Loc::root(root)) {
                    if let Some(theirs) = b.fact(Loc::root(root), fact.key()) {
                        assert_eq!(j.fact(Loc::root(root), fact.key()).cloned(), fact.join(theirs));
                    }
                }
            }
        }
    }

    /// An operation that only adds to what is known, if one applies.
    fn add(rng: &mut Rng, c: &mut C) -> bool {
        let root = ROOTS[rng.below(ROOTS.len() as u64) as usize];
        let other = ROOTS[rng.below(ROOTS.len() as u64) as usize];
        if rng.below(2) == 0 {
            if root == other || !c.members(Loc::root(root)).eq(&[root]) || !c.facts(Loc::root(root)).is_empty() || c.find(Loc::root(root)).is_some() {
                return false;
            }
            c.assign(root, Loc::root(other));
        } else {
            let fact = FACTS[rng.below(FACTS.len() as u64) as usize].clone();
            if c.fact(Loc::root(root), fact.key()).is_some() {
                return false;
            }
            c.learn(Loc::root(root), fact);
        }
        true
    }

    #[test]
    fn knowing_more_is_accepted_and_not_the_other_way() {
        let mut rng = Rng(4242);
        for _ in 0..1000 {
            let (a, _) = random(&mut rng, 25);
            assert!(a.accepts(&a));
            let mut b = a.clone();
            if !(0..8).any(|_| add(&mut rng, &mut b)) {
                continue;
            }
            assert!(a.accepts(&b), "{a:?} doesn't accept more, {b:?}");
            assert!(!b.accepts(&a), "{b:?} accepts less, {a:?}");
            let mut c = b.clone();
            if (0..8).any(|_| add(&mut rng, &mut c)) {
                assert!(a.accepts(&c), "accepting isn't transitive: {a:?}, {b:?}, {c:?}");
            }
        }
    }

    #[test]
    fn lowering_one_fact_domain_leaves_the_rest() {
        let mut rng = Rng(0x51ed);
        let places = places();
        for _ in 0..1000 {
            let (before, _) = random(&mut rng, 30);
            let (above, _) = random(&mut rng, 30);
            let key = rng.below(2) as u8;
            let mut lowered = before.clone();
            lowered.lower_facts(key, &above);
            let mut again = lowered.clone();
            again.lower_facts(key, &above);
            assert_eq!(again, lowered, "lowering twice is lowering once");
            let mut towards_itself = before.clone();
            towards_itself.lower_facts(key, &before);
            assert_eq!(towards_itself, before, "lowering towards itself forgets nothing");
            for (root, path) in &places {
                let at = Loc { root: *root, path };
                for other_key in [0u8, 1] {
                    let kept = lowered.fact(at, other_key);
                    if other_key == key {
                        if let Some(fact) = kept {
                            assert_eq!(before.fact(at, key), Some(fact), "{at:?} learned {fact:?}");
                            assert_eq!(above.fact(at, key), Some(fact), "{at:?} kept {fact:?}, which {above:?} doesn't have");
                        }
                    } else {
                        assert_eq!(kept, before.fact(at, other_key), "{at:?}'s other domain changed");
                    }
                }
                for (other, other_path) in &places {
                    let theirs = Loc { root: *other, path: other_path };
                    assert_eq!(lowered.same(at, theirs), before.same(at, theirs), "the classes changed");
                }
            }
        }
    }

    #[test]
    fn lowering_the_partition_keeps_every_fact() {
        let mut rng = Rng(0xc0ffee);
        let places = places();
        for _ in 0..1000 {
            let (before, _) = random(&mut rng, 30);
            let (above, _) = random(&mut rng, 30);
            let mut lowered = before.clone();
            lowered.lower_partition(&above);
            let mut again = lowered.clone();
            again.lower_partition(&above);
            assert_eq!(again, lowered, "lowering twice is lowering once");
            let mut towards_itself = before.clone();
            towards_itself.lower_partition(&before);
            assert_eq!(towards_itself, before, "lowering towards itself forgets nothing");
            for (root, path) in &places {
                let at = Loc { root: *root, path };
                assert_eq!(lowered.facts(at), before.facts(at), "{at:?} lost a fact lowering {before:?} towards {above:?}");
                for (other, other_path) in &places {
                    let theirs = Loc { root: *other, path: other_path };
                    let (now, was, there) = (lowered.same(at, theirs), before.same(at, theirs), above.same(at, theirs));
                    assert!(!now || was, "{at:?} and {theirs:?} became equal");
                    if was && there {
                        assert!(now, "{at:?} and {theirs:?} are equal in both {before:?} and {above:?}, not in {lowered:?}");
                    }
                    if now && !there {
                        assert!(above.find(at).is_none() && above.find(theirs).is_none(), "{at:?} and {theirs:?} are kept equal, which {above:?} knows aren't");
                    }
                }
            }
        }
    }

    #[test]
    fn a_view_sees_what_it_maps() {
        let mut rng = Rng(99);
        for _ in 0..500 {
            let (c, _) = random(&mut rng, 30);
            let field = [Label::Upvalue(0)];
            let map = [
                (Root::Slot(0), slot(2)),
                (Root::Slot(1), slot(3)),
                (Root::Upvalue(0), Loc { root: Root::Slot(2), path: &field }),
            ];
            let v = c.view(&map);
            for &(mine, at) in &map {
                assert_eq!(v.facts(Loc::root(mine)), c.facts(at));
                for &(other, other_at) in &map {
                    assert_eq!(v.same(Loc::root(mine), Loc::root(other)), mine == other || c.same(at, other_at));
                }
            }
            for root in [Root::Slot(2), Root::Slot(3), Root::Upvalue(1)] {
                assert!(v.facts(Loc::root(root)).is_empty() && v.members(Loc::root(root)) == vec![root], "{root:?} isn't mapped");
            }
        }
    }

    #[test]
    fn an_overlay_replaces_only_what_it_maps() {
        let mut rng = Rng(1234);
        for _ in 0..500 {
            let (mut c, _) = random(&mut rng, 30);
            let (other, _) = random(&mut rng, 30);
            let before = c.clone();
            let map = [(Root::Slot(0), slot(1)), (Root::Upvalue(0), slot(2))];
            c.overlay(&other, &map);
            for &(mine, at) in &map {
                assert_eq!(c.facts(Loc::root(mine)), other.facts(at));
            }
            assert_eq!(c.same(Loc::root(Root::Slot(0)), Loc::root(Root::Upvalue(0))), other.same(slot(1), slot(2)));
            for root in [Root::Slot(1), Root::Slot(2), Root::Slot(3), Root::Upvalue(1)] {
                assert_eq!(c.facts(Loc::root(root)), before.facts(Loc::root(root)));
                for other_root in [Root::Slot(1), Root::Slot(2), Root::Slot(3), Root::Upvalue(1)] {
                    assert_eq!(c.same(Loc::root(root), Loc::root(other_root)), before.same(Loc::root(root), Loc::root(other_root)));
                }
                assert!(!c.same(Loc::root(root), Loc::root(Root::Slot(0))));
            }
        }
    }
}
