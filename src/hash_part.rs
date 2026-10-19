//! A table's hash part: an insertion-ordered map JIT code reads by its layout. See Note [Hash
//! part layout].

use std::hash::{BuildHasher, Hash};

use crate::lboxed::LBoxed;
use crate::vm::{InternedHasher, LCanon};

// Note [Hash part layout]
// ~~~~~~~~~~~~~~~~~~~~~~~
// A table's hash part is a compact dict: its entries, each a key and its value, kept densely in
// the order their keys were first inserted, and an index table over them. The index table has a
// power-of-two count of slots, each 0 for an empty slot or an entry's position plus one. A key is
// found by probing linearly from its hash masked to the slots, until a slot names the key's entry
// or is empty: a key the table lacks ends at an empty slot. Keys are canonical (Note [Canonical
// values]), so an entry is the key's when its key has the same bits.
//
// No more than half the slots are used, so a probe ends soon, and the first slot probed is often
// empty for a missing key. An entry keeps its position until the part is cleared, as no key is
// removed: a key set to nil keeps its entry. The entries move only when an insertion outgrows
// their room or the part is cleared, as the table's epoch tells (Note [Hash witnesses]).
//
// An empty part's index table is a shared one of a single empty slot, so a probe needs no check
// that there is one. JIT code reads every field at its offset, so the layout is fixed (`repr(C)`):
// it checks a predicted entry's key, and a missing key's first slot, without a call.

/// A key and its value, as JIT code reads them. See Note [Hash part layout].
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct Entry<'src, 'intern> {
    pub key: LCanon<'src, 'intern>,
    pub value: LBoxed<'src, 'intern>,
}

/// The index table of every empty hash part: one empty slot, never written. See Note [Hash part
/// layout].
static EMPTY: [u32; 1] = [0];

/// A table's hash part. See Note [Hash part layout].
#[repr(C)]
pub struct HashPart<'src, 'intern> {
    /// The entries, `len` of them in room for `cap`.
    pub entries: *mut Entry<'src, 'intern>,
    pub len: usize,
    cap: usize,
    /// The index table, of `mask + 1` slots.
    pub indices: *mut u32,
    pub mask: usize,
}

impl<'src, 'intern> HashPart<'src, 'intern> {
    pub fn new() -> Self {
        HashPart { entries: std::ptr::NonNull::dangling().as_ptr(), len: 0, cap: 0, indices: EMPTY.as_ptr().cast_mut(), mask: 0 }
    }

    /// One with room for `capacity` entries before it grows.
    pub fn with_capacity(capacity: usize) -> Self {
        let mut part = Self::new();
        if capacity > 0 {
            part.grow_to(capacity.next_power_of_two());
        }
        part
    }

    /// The hash of a key, as every lookup and the JIT's checks compute it.
    pub fn hash(key: &impl Hash) -> u64 {
        InternedHasher::default().hash_one(key)
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    fn entries(&self) -> &[Entry<'src, 'intern>] {
        // SAFETY: `entries` holds `len` initialized entries.
        unsafe { std::slice::from_raw_parts(self.entries, self.len) }
    }

    fn entries_mut(&mut self) -> &mut [Entry<'src, 'intern>] {
        // SAFETY: as `entries`, and borrowed uniquely through `self`.
        unsafe { std::slice::from_raw_parts_mut(self.entries, self.len) }
    }

    fn slots(&self) -> &[u32] {
        // SAFETY: `indices` has `mask + 1` slots.
        unsafe { std::slice::from_raw_parts(self.indices, self.mask + 1) }
    }

    /// The position of the entry `is` says is the one wanted, among the keys of hash `hash`.
    pub fn find(&self, hash: u64, is: impl Fn(&LCanon<'src, 'intern>) -> bool) -> Option<usize> {
        let (slots, entries) = (self.slots(), self.entries());
        let mut at = hash as usize & self.mask;
        loop {
            match slots[at] {
                0 => return None,
                slot if is(&entries[slot as usize - 1].key) => return Some(slot as usize - 1),
                _ => at = (at + 1) & self.mask,
            }
        }
    }

    pub fn get_index_of(&self, key: &LCanon<'src, 'intern>) -> Option<usize> {
        self.find(Self::hash(key), |k| k == key)
    }

    pub fn get(&self, key: &LCanon<'src, 'intern>) -> Option<&LBoxed<'src, 'intern>> {
        self.get_index_of(key).map(|at| &self.entries()[at].value)
    }

    pub fn contains_key(&self, key: &LCanon<'src, 'intern>) -> bool {
        self.get_index_of(key).is_some()
    }

    /// The position of `key`'s entry, and its value.
    pub fn get_full_mut(&mut self, key: &LCanon<'src, 'intern>) -> Option<(usize, &mut LBoxed<'src, 'intern>)> {
        let at = self.get_index_of(key)?;
        Some((at, &mut self.entries_mut()[at].value))
    }

    pub fn get_index(&self, at: usize) -> Option<(&LCanon<'src, 'intern>, &LBoxed<'src, 'intern>)> {
        self.entries().get(at).map(|entry| (&entry.key, &entry.value))
    }

    pub fn get_index_mut(&mut self, at: usize) -> Option<(&LCanon<'src, 'intern>, &mut LBoxed<'src, 'intern>)> {
        self.entries_mut().get_mut(at).map(|entry| (&entry.key, &mut entry.value))
    }

    /// Set `key`'s value, giving its old value, or append its entry if it has none.
    pub fn insert(&mut self, key: LCanon<'src, 'intern>, value: LBoxed<'src, 'intern>) -> Option<LBoxed<'src, 'intern>> {
        let hash = Self::hash(&key);
        if let Some(at) = self.find(hash, |k| *k == key) {
            return Some(std::mem::replace(&mut self.entries_mut()[at].value, value));
        }
        if self.len == self.cap {
            self.grow_to((self.cap * 2).max(4));
        }
        // SAFETY: there is room for one more entry.
        unsafe { self.entries.add(self.len).write(Entry { key, value }) };
        self.len += 1;
        self.place(hash, self.len as u32);
        None
    }

    /// Point the first empty slot of `hash`'s probe at the entry `slot` names.
    fn place(&mut self, hash: u64, slot: u32) {
        // SAFETY: a part with an entry has an index table of its own.
        let slots = unsafe { std::slice::from_raw_parts_mut(self.indices, self.mask + 1) };
        let mut at = hash as usize & self.mask;
        while slots[at] != 0 {
            at = (at + 1) & self.mask;
        }
        slots[at] = slot;
    }

    /// Make room for `cap` entries, a power of two, with an index table of twice as many slots.
    fn grow_to(&mut self, cap: usize) {
        debug_assert!(cap.is_power_of_two() && cap >= self.len);
        let mut entries = self.take_entries();
        entries.reserve_exact(cap - entries.len());
        let mut entries = std::mem::ManuallyDrop::new(entries);
        (self.entries, self.cap) = (entries.as_mut_ptr(), entries.capacity());
        self.free_indices();
        let mut indices = std::mem::ManuallyDrop::new(vec![0u32; cap * 2]);
        (self.indices, self.mask) = (indices.as_mut_ptr(), cap * 2 - 1);
        for slot in 1..=self.len {
            let hash = Self::hash(&self.entries()[slot - 1].key);
            self.place(hash, slot as u32);
        }
    }

    /// Its entries as the `Vec` holding them, leaving it none.
    fn take_entries(&mut self) -> Vec<Entry<'src, 'intern>> {
        // SAFETY: the entries were a `Vec` of `cap`, `len` of them initialized, or none.
        let entries = if self.cap == 0 { Vec::new() } else { unsafe { Vec::from_raw_parts(self.entries, self.len, self.cap) } };
        (self.entries, self.cap) = (std::ptr::NonNull::dangling().as_ptr(), 0);
        entries
    }

    /// Free its index table, if it has one of its own.
    fn free_indices(&mut self) {
        if !std::ptr::eq(self.indices, EMPTY.as_ptr()) {
            // SAFETY: an index table of its own is a `Vec` of `mask + 1` slots.
            drop(unsafe { Vec::from_raw_parts(self.indices, self.mask + 1, self.mask + 1) });
        }
        (self.indices, self.mask) = (EMPTY.as_ptr().cast_mut(), 0);
    }

    /// Drop every entry, keeping their room.
    pub fn clear(&mut self) {
        self.len = 0;
        if !std::ptr::eq(self.indices, EMPTY.as_ptr()) {
            // SAFETY: an index table of its own, which this owns.
            unsafe { std::slice::from_raw_parts_mut(self.indices, self.mask + 1) }.fill(0);
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (&LCanon<'src, 'intern>, &LBoxed<'src, 'intern>)> {
        self.entries().iter().map(|entry| (&entry.key, &entry.value))
    }

    pub fn keys(&self) -> impl Iterator<Item = &LCanon<'src, 'intern>> {
        self.entries().iter().map(|entry| &entry.key)
    }
}

impl Default for HashPart<'_, '_> {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for HashPart<'_, '_> {
    fn drop(&mut self) {
        drop(self.take_entries());
        self.free_indices();
    }
}

impl<'src, 'intern> FromIterator<(LCanon<'src, 'intern>, LBoxed<'src, 'intern>)> for HashPart<'src, 'intern> {
    fn from_iter<I: IntoIterator<Item = (LCanon<'src, 'intern>, LBoxed<'src, 'intern>)>>(entries: I) -> Self {
        let mut part = HashPart::new();
        for (key, value) in entries {
            part.insert(key, value);
        }
        part
    }
}

impl std::fmt::Debug for HashPart<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    fn number(n: f64) -> LCanon<'static, 'static> {
        LCanon::constant(&crate::chunk::Constant::Number(crate::vm::Number(n)))
    }

    fn value(n: i32) -> LBoxed<'static, 'static> {
        LBoxed::from_int(n)
    }

    /// Every key is found where it was put, in the order it was first put, against a reference.
    fn agrees(part: &HashPart, reference: &HashMap<u64, i32>, order: &[u64]) {
        assert_eq!(part.len(), order.len());
        for (at, &bits) in order.iter().enumerate() {
            let key = unsafe { LCanon::from_bits(bits) };
            assert_eq!(part.get_index_of(&key), Some(at), "{key:?}'s position");
            assert_eq!(part.get(&key).map(|v| v.bits()), Some(value(reference[&bits]).bits()));
            assert_eq!(part.get_index(at).map(|(k, _)| k.boxed().bits()), Some(bits));
        }
        assert_eq!(part.keys().map(|k| k.boxed().bits()).collect::<Vec<_>>(), order);
    }

    #[test]
    fn an_empty_part_finds_nothing() {
        let part = HashPart::new();
        assert!(part.is_empty() && part.get(&number(1.5)).is_none() && part.get_index(0).is_none());
        assert_eq!(part.mask, 0);
        assert_eq!(unsafe { *part.indices }, 0, "an empty part's one slot is empty");
    }

    #[test]
    fn keys_keep_their_order_and_positions_as_it_grows() {
        let mut part = HashPart::new();
        let (mut reference, mut order) = (HashMap::new(), Vec::new());
        for i in 0..2000 {
            let key = number(i as f64 + 0.5);
            assert!(part.insert(key, value(i)).is_none());
            reference.insert(key.boxed().bits(), i);
            order.push(key.boxed().bits());
            assert!(part.len() * 2 <= part.mask + 1, "half its slots at most are used");
        }
        agrees(&part, &reference, &order);
    }

    #[test]
    fn a_key_put_again_keeps_its_entry() {
        let mut part = HashPart::new();
        for i in 0..100 {
            part.insert(number(i as f64 + 0.25), value(i));
        }
        let entries = part.entries;
        for i in 0..100 {
            assert_eq!(part.insert(number(i as f64 + 0.25), value(-i)).map(|v| v.bits()), Some(value(i).bits()));
        }
        assert_eq!(part.entries, entries, "no entry moved");
        let order: Vec<u64> = (0..100).map(|i| number(i as f64 + 0.25).boxed().bits()).collect();
        let reference = order.iter().enumerate().map(|(i, &bits)| (bits, -(i as i32))).collect();
        agrees(&part, &reference, &order);
    }

    /// Keys whose hashes share their low bits all probe from one slot, and each is still found,
    /// as is a key missing among them.
    #[test]
    fn colliding_keys_are_each_found() {
        let mut part = HashPart::with_capacity(64);
        let mask = part.mask as u64;
        let first = HashPart::hash(&number(1.0)) & mask;
        let colliding: Vec<LCanon> = (0..100_000).map(|i| number(i as f64)).filter(|k| HashPart::hash(k) & mask == first).take(20).collect();
        assert_eq!(colliding.len(), 20);
        for (i, &key) in colliding.iter().enumerate() {
            part.insert(key, value(i as i32));
        }
        assert_eq!(part.mask as u64, mask, "it fits without growing");
        for (i, key) in colliding.iter().enumerate() {
            assert_eq!(part.get_index_of(key), Some(i));
        }
        let missing = (100_000..).map(|i| number(i as f64)).find(|k| HashPart::hash(k) & mask == first).unwrap();
        assert!(part.get(&missing).is_none());
    }

    #[test]
    fn cleared_it_keeps_its_room_and_finds_nothing() {
        let mut part = HashPart::with_capacity(8);
        for i in 0..8 {
            part.insert(number(i as f64 + 0.5), value(i));
        }
        let (entries, mask) = (part.entries, part.mask);
        part.clear();
        assert!(part.is_empty() && part.get(&number(0.5)).is_none());
        part.insert(number(9.5), value(9));
        assert_eq!((part.entries, part.mask), (entries, mask));
        assert_eq!(part.get_index_of(&number(9.5)), Some(0));
    }

    #[test]
    fn strings_are_found_by_their_bytes() {
        let arena = internment::Arena::new();
        let arena: &'static internment::Arena<crate::vm::IStr<'static>> = Box::leak(Box::new(arena));
        let mut part = HashPart::new();
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
