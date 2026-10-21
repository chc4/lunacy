//! A table's hash part: a map keeping its keys in insertion order. See Note [Hash part layout].

use std::hash::BuildHasher;

use crate::lboxed::LBoxed;
use crate::vm::{InternedHasher, LCanon};

// Note [Hash part layout]
// ~~~~~~~~~~~~~~~~~~~~~~~
// A table's hash part stores its key-value pairs in the order their keys were first inserted, and
// a hash table mapping each key to its pair's index. The hash table has a power-of-two count of
// slots, each empty or holding a pair's index. It uses Robin Hood hashing, with no key further past
// the slot its hash masks to than log2 of the slot count, so a lookup probes at most that many
// slots after its first, and stops at an empty one. An insertion that would place a key further,
// or fill more than seven eighths of the slots, doubles the hash table. Keys are canonical (Note [Canonical values]), so a pair is a key's when its key has the same
// bits.
//
// No key is removed: a key set to nil keeps its pair, so a pair's index doesn't change until the
// part is cleared. Inserting a key may reallocate the key-value storage, so it increments the
// table's epoch, which invalidates any outstanding hash keys (Note [Hash witnesses]).
//
// An empty part's hash table is a shared one of a single empty slot, so a lookup needs no check
// that there is one.

/// A key and its value. See Note [Hash part layout].
#[derive(Debug, Clone, Copy)]
struct Pair<'src, 'intern> {
    key: LCanon<'src, 'intern>,
    value: LBoxed<'src, 'intern>,
}

/// The hash table of every empty hash part: one empty slot, never written. See Note [Hash part
/// layout].
static EMPTY: [u32; 1] = [0];

/// A table's hash part. See Note [Hash part layout].
pub struct HashPart<'src, 'intern, S = InternedHasher> {
    /// The key-value pairs, `len` of them in room for `cap`.
    pairs: *mut Pair<'src, 'intern>,
    len: usize,
    cap: usize,
    /// The hash table, of `mask + 1` slots, each 0 for an empty slot or a pair's index plus one.
    table: *mut u32,
    mask: usize,
    hasher: S,
}

impl<'src, 'intern, S> HashPart<'src, 'intern, S> {
    pub fn with_hasher(hasher: S) -> Self {
        HashPart { pairs: std::ptr::NonNull::dangling().as_ptr(), len: 0, cap: 0, table: EMPTY.as_ptr().cast_mut(), mask: 0, hasher }
    }

    pub fn hasher(&self) -> &S {
        &self.hasher
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    fn pairs(&self) -> &[Pair<'src, 'intern>] {
        // SAFETY: `pairs` holds `len` initialized pairs.
        unsafe { std::slice::from_raw_parts(self.pairs, self.len) }
    }

    fn pairs_mut(&mut self) -> &mut [Pair<'src, 'intern>] {
        // SAFETY: as `pairs`, and borrowed uniquely through `self`.
        unsafe { std::slice::from_raw_parts_mut(self.pairs, self.len) }
    }

    fn slots(&self) -> &[u32] {
        // SAFETY: `table` has `mask + 1` slots.
        unsafe { std::slice::from_raw_parts(self.table, self.mask + 1) }
    }

    pub fn get_index(&self, at: usize) -> Option<(&LCanon<'src, 'intern>, &LBoxed<'src, 'intern>)> {
        self.pairs().get(at).map(|pair| (&pair.key, &pair.value))
    }

    pub fn get_index_mut(&mut self, at: usize) -> Option<(&LCanon<'src, 'intern>, &mut LBoxed<'src, 'intern>)> {
        self.pairs_mut().get_mut(at).map(|pair| (&pair.key, &mut pair.value))
    }

    /// Remove every pair, maintaining capacity.
    pub fn clear(&mut self) {
        self.len = 0;
        if !std::ptr::eq(self.table, EMPTY.as_ptr()) {
            // SAFETY: a hash table of its own, which this owns.
            unsafe { std::slice::from_raw_parts_mut(self.table, self.mask + 1) }.fill(0);
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (&LCanon<'src, 'intern>, &LBoxed<'src, 'intern>)> {
        self.pairs().iter().map(|pair| (&pair.key, &pair.value))
    }

    pub fn keys(&self) -> impl Iterator<Item = &LCanon<'src, 'intern>> {
        self.pairs().iter().map(|pair| &pair.key)
    }

    /// Its pairs as the `Vec` holding them, leaving it none.
    fn take_pairs(&mut self) -> Vec<Pair<'src, 'intern>> {
        let pairs = std::mem::replace(&mut self.pairs, std::ptr::NonNull::dangling().as_ptr());
        let cap = std::mem::replace(&mut self.cap, 0);
        // SAFETY: the pairs were a `Vec` of `cap`, `len` of them initialized, or none.
        if cap == 0 { Vec::new() } else { unsafe { Vec::from_raw_parts(pairs, self.len, cap) } }
    }

    /// Free its hash table, if it has one of its own, leaving it the empty one.
    fn free_table(&mut self) {
        let table = std::mem::replace(&mut self.table, EMPTY.as_ptr().cast_mut());
        let slots = std::mem::replace(&mut self.mask, 0) + 1;
        if !std::ptr::eq(table, EMPTY.as_ptr()) {
            // SAFETY: a hash table of its own is a `Vec` of its slots.
            drop(unsafe { Vec::from_raw_parts(table, slots, slots) });
        }
    }

    /// Make room for `cap` pairs.
    fn grow_pairs(&mut self, cap: usize) {
        let mut pairs = self.take_pairs();
        pairs.reserve_exact(cap - pairs.len());
        let mut pairs = std::mem::ManuallyDrop::new(pairs);
        (self.pairs, self.cap) = (pairs.as_mut_ptr(), pairs.capacity());
    }
}

impl<'src, 'intern, S: BuildHasher + Default> HashPart<'src, 'intern, S> {
    pub fn new() -> Self {
        Self::with_hasher(S::default())
    }

    /// One with capacity for `capacity` pairs.
    pub fn with_capacity(capacity: usize) -> Self {
        let mut part = Self::new();
        if capacity > 0 {
            part.grow_pairs(capacity.next_power_of_two());
            part.rebuild((capacity + capacity / 7).next_power_of_two().max(4));
        }
        part
    }
}

impl<'src, 'intern, S: BuildHasher> HashPart<'src, 'intern, S> {
    /// The index of the pair whose key `is` accepts, among the keys of hash `hash` by `hasher`.
    pub fn find(&self, hash: u64, is: impl Fn(&LCanon<'src, 'intern>) -> bool) -> Option<usize> {
        let (slots, pairs) = (self.slots(), self.pairs());
        let mut at = hash as usize & self.mask;
        for _ in 0..=self.max_displacement() {
            match slots[at] {
                0 => return None,
                slot if is(&pairs[slot as usize - 1].key) => return Some(slot as usize - 1),
                _ => at = (at + 1) & self.mask,
            }
        }
        None
    }

    pub fn get_index_of(&self, key: &LCanon<'src, 'intern>) -> Option<usize> {
        self.find(self.hasher.hash_one(key), |k| k == key)
    }

    pub fn get(&self, key: &LCanon<'src, 'intern>) -> Option<&LBoxed<'src, 'intern>> {
        self.get_index_of(key).map(|at| &self.pairs()[at].value)
    }

    pub fn contains_key(&self, key: &LCanon<'src, 'intern>) -> bool {
        self.get_index_of(key).is_some()
    }

    /// The index of `key`'s pair, and its value.
    pub fn get_full_mut(&mut self, key: &LCanon<'src, 'intern>) -> Option<(usize, &mut LBoxed<'src, 'intern>)> {
        let at = self.get_index_of(key)?;
        Some((at, &mut self.pairs_mut()[at].value))
    }

    /// Set `key`'s value, giving its old value, or append its pair if it has none.
    pub fn insert(&mut self, key: LCanon<'src, 'intern>, value: LBoxed<'src, 'intern>) -> Option<LBoxed<'src, 'intern>> {
        let hash = self.hasher.hash_one(key);
        if let Some(at) = self.find(hash, |k| *k == key) {
            return Some(std::mem::replace(&mut self.pairs_mut()[at].value, value));
        }
        if self.len == self.cap {
            self.grow_pairs((self.cap * 2).max(4));
        }
        // SAFETY: there is room for one more pair.
        unsafe { self.pairs.add(self.len).write(Pair { key, value }) };
        self.len += 1;
        let full = self.len * 8 > (self.mask + 1) * 7;
        if std::ptr::eq(self.table, EMPTY.as_ptr()) || full || !self.place(hash, self.len as u32) {
            self.rebuild(((self.mask + 1) * 2).max(4));
        }
        None
    }

    /// How many slots past the one its hash masks to a key may be: log2 of the slot count.
    fn max_displacement(&self) -> usize {
        (self.mask + 1).trailing_zeros() as usize
    }

    /// The hash of the key of the pair `slot` names.
    fn slot_hash(&self, slot: u32) -> u64 {
        self.hasher.hash_one(self.pairs()[slot as usize - 1].key)
    }

    /// Put the pair `slot` names, of hash `hash`, into the hash table, taking the slot of any key
    /// nearer its own and moving that key on. False if a key would be further than
    /// `max_displacement` from its own slot, leaving the hash table to be rebuilt.
    fn place(&mut self, hash: u64, mut slot: u32) -> bool {
        debug_assert!(!std::ptr::eq(self.table, EMPTY.as_ptr()));
        let (table, mask) = (self.table, self.mask);
        let mut at = hash as usize & mask;
        let mut displacement = 0;
        while displacement <= self.max_displacement() {
            // SAFETY: `at` is masked to the hash table's slots, and the table is its own.
            let resident = unsafe { *table.add(at) };
            if resident == 0 {
                unsafe { *table.add(at) = slot };
                return true;
            }
            let theirs = at.wrapping_sub(self.slot_hash(resident) as usize) & mask;
            if theirs < displacement {
                unsafe { *table.add(at) = slot };
                (slot, displacement) = (resident, theirs);
            }
            at = (at + 1) & mask;
            displacement += 1;
        }
        false
    }

    /// Rebuild the hash table with `slots` slots, a power of two, doubling them until every key
    /// fits within `max_displacement` of its own slot.
    fn rebuild(&mut self, mut slots: usize) {
        loop {
            self.free_table();
            let mut table = std::mem::ManuallyDrop::new(vec![0u32; slots]);
            (self.table, self.mask) = (table.as_mut_ptr(), slots - 1);
            if (1..=self.len as u32).all(|slot| self.place(self.slot_hash(slot), slot)) {
                return;
            }
            slots *= 2;
        }
    }
}

impl<S: BuildHasher + Default> Default for HashPart<'_, '_, S> {
    fn default() -> Self {
        Self::new()
    }
}

impl<S> Drop for HashPart<'_, '_, S> {
    fn drop(&mut self) {
        drop(self.take_pairs());
        self.free_table();
    }
}

impl<'src, 'intern, S: BuildHasher + Default> FromIterator<(LCanon<'src, 'intern>, LBoxed<'src, 'intern>)> for HashPart<'src, 'intern, S> {
    fn from_iter<I: IntoIterator<Item = (LCanon<'src, 'intern>, LBoxed<'src, 'intern>)>>(pairs: I) -> Self {
        let mut part = HashPart::new();
        for (key, value) in pairs {
            part.insert(key, value);
        }
        part
    }
}

impl<S> std::fmt::Debug for HashPart<'_, '_, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    type Part = HashPart<'static, 'static>;

    fn number(n: f64) -> LCanon<'static, 'static> {
        LCanon::constant(&crate::chunk::Constant::Number(crate::vm::Number(n)))
    }

    fn value(n: i32) -> LBoxed<'static, 'static> {
        LBoxed::from_int(n)
    }

    /// Every key is found where it was put, in the order it was first put, against a reference,
    /// and no key is further than `max_displacement` from its own slot.
    fn agrees(part: &Part, reference: &HashMap<u64, i32>, order: &[u64]) {
        assert_eq!(part.len(), order.len());
        for (at, &bits) in order.iter().enumerate() {
            let key = unsafe { LCanon::from_bits(bits) };
            assert_eq!(part.get_index_of(&key), Some(at), "{key:?}'s index");
            assert_eq!(part.get(&key).map(|v| v.bits()), Some(value(reference[&bits]).bits()));
            assert_eq!(part.get_index(at).map(|(k, _)| k.boxed().bits()), Some(bits));
        }
        assert_eq!(part.keys().map(|k| k.boxed().bits()).collect::<Vec<_>>(), order);
        for (at, &slot) in part.slots().iter().enumerate().filter(|(_, slot)| **slot != 0) {
            assert!(at.wrapping_sub(part.slot_hash(slot) as usize) & part.mask <= part.max_displacement());
        }
    }

    #[test]
    fn an_empty_part_finds_nothing() {
        let part = Part::new();
        assert!(part.is_empty() && part.get(&number(1.5)).is_none() && part.get_index(0).is_none());
        assert_eq!(part.mask, 0);
        assert_eq!(unsafe { *part.table }, 0, "an empty part's one slot is empty");
    }

    #[test]
    fn keys_keep_their_order_and_indices_as_it_grows() {
        let mut part = Part::new();
        let (mut reference, mut order) = (HashMap::new(), Vec::new());
        // Integers below 1, which a table keeps in its hash part.
        for i in 0..2000 {
            let key = number(-i as f64);
            assert!(part.insert(key, value(i)).is_none());
            reference.insert(key.boxed().bits(), i);
            order.push(key.boxed().bits());
        }
        agrees(&part, &reference, &order);
    }

    #[test]
    fn a_key_put_again_keeps_its_pair() {
        let mut part = Part::new();
        for i in 0..100 {
            part.insert(number(i as f64 + 0.25), value(i));
        }
        let pairs = part.pairs;
        for i in 0..100 {
            assert_eq!(part.insert(number(i as f64 + 0.25), value(-i)).map(|v| v.bits()), Some(value(i).bits()));
        }
        assert_eq!(part.pairs, pairs, "no pair moved");
        let order: Vec<u64> = (0..100).map(|i| number(i as f64 + 0.25).boxed().bits()).collect();
        let reference = order.iter().enumerate().map(|(i, &bits)| (bits, -(i as i32))).collect();
        agrees(&part, &reference, &order);
    }

    /// Keys whose hashes share their low bits grow the hash table until they're each near their
    /// own slot, and each is found, as is a key missing among them.
    #[test]
    fn colliding_keys_are_each_found() {
        let mut part = Part::with_capacity(64);
        let mask = part.mask as u64;
        let hash = |k: &LCanon| part.hasher().hash_one(k);
        let first = hash(&number(1.0)) & mask;
        let colliding: Vec<LCanon> = (0..100_000).map(|i| number(i as f64)).filter(|k| hash(k) & mask == first).take(20).collect();
        let missing = (100_000..).map(|i| number(i as f64)).find(|k| hash(k) & mask == first).unwrap();
        assert_eq!(colliding.len(), 20);
        for (i, &key) in colliding.iter().enumerate() {
            part.insert(key, value(i as i32));
        }
        let order: Vec<u64> = colliding.iter().map(|k| k.boxed().bits()).collect();
        let reference = order.iter().enumerate().map(|(i, &bits)| (bits, i as i32)).collect();
        agrees(&part, &reference, &order);
        assert!(part.get(&missing).is_none());
    }

    #[test]
    fn cleared_it_keeps_its_capacity_and_finds_nothing() {
        let mut part = Part::with_capacity(8);
        for i in 0..8 {
            part.insert(number(i as f64 + 0.5), value(i));
        }
        let (pairs, mask) = (part.pairs, part.mask);
        part.clear();
        assert!(part.is_empty() && part.get(&number(0.5)).is_none());
        part.insert(number(9.5), value(9));
        assert_eq!((part.pairs, part.mask), (pairs, mask));
        assert_eq!(part.get_index_of(&number(9.5)), Some(0));
    }

    #[test]
    fn strings_are_found_by_their_bytes() {
        let arena = internment::Arena::new();
        let arena: &'static internment::Arena<crate::vm::IStr<'static>> = Box::leak(Box::new(arena));
        let mut part = Part::new();
        let keys: Vec<LCanon> = (0..300).map(|i| LCanon::new(LBoxed::interned(crate::vm::intern_bytes(arena, format!("k{i}").as_bytes())), arena)).collect();
        for (i, &key) in keys.iter().enumerate() {
            part.insert(key, value(i as i32));
        }
        for (i, key) in keys.iter().enumerate() {
            let again = LCanon::new(LBoxed::interned(crate::vm::intern_bytes(arena, format!("k{i}").as_bytes())), arena);
            assert_eq!(again.boxed().bits(), key.boxed().bits(), "interned once");
            assert_eq!(part.get_index_of(&again), Some(i));
        }
    }
}
