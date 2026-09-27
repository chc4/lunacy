#![allow(non_snake_case, non_camel_case_types, unused)]
use core::fmt::Debug;
use core::hash::Hash;
use std::collections::hash_map::Entry;
use std::num::Wrapping;
use std::ops::{DerefMut, Index, IndexMut};
use std::marker::PhantomData;
use crate::chunk::FunctionBlock;
use crate::chunk::{InstBits, Constant};
use crate::stack::ValueStack;
use rustc_hash::FxBuildHasher;
use std::borrow::Cow;
use std::cell::{RefCell, Cell};
use std::collections::HashMap;
use std::hash::BuildHasher;
use std::{error::Error, ops::Deref};
use std::io::Write;

use internment::ArenaIntern;
use indexmap::IndexMap;

use qcell::{LCell, LCellOwner};
use crate::{TLCell, TlcOwner, Owner};

use crate::generator::{Specializer, Context, SubPc};

// `BlockId` and `HashRef` are referenced by `ReturnLocation` / `HashWitness`, so they
// live here rather than in the generator module (which re-imports them).
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash, Debug)]
pub struct BlockId(pub usize);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HashRef(pub u8);
use crate::perf::PerfCounters;
use crate::gc::{Mark, Heap, Gc, GcCtx};
pub use crate::gc::LStr;
use crate::{debug, warn};

pub type LConstant<'src, 'intern> = Constant<internment::ArenaIntern<'intern, IStr<'src>>>;

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct Number(pub f64);

impl Hash for Number {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.0.to_bits())
    }
}

impl Eq for Number {
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, core::marker::ConstParamTy)]
pub enum Opcode {
    MOVE = 0,
    LOADK,
    LOADBOOL,
    LOADNIL,
    GETUPVAL,
    GETGLOBAL,
    GETTABLE,
    SETGLOBAL,
    SETUPVAL,
    SETTABLE,
    NEWTABLE,
    SELF,
    ADD,
    SUB,
    MUL,
    DIV,
    MOD,
    POW,
    UNM,
    NOT,
    LEN,
    CONCAT,
    JMP,
    EQ,
    LT,
    LE,
    TEST,
    TESTSET,
    CALL,
    TAILCALL,
    RETURN,
    FORLOOP,
    FORPREP,
    TFORLOOP,
    SETLIST,
    CLOSE,
    CLOSURE,
    VARARG,

    INVALID,
}

impl From<u8> for Opcode {
    fn from(value: u8) -> Self {
        // this is stupid: despite us specifying 6 bits in the bitfield, the into
        // clause doesn't shift out before calling From. why! whats the point of
        // the bit specifiers then!
        let value = value & 0b111111;
        if value <= (Opcode::VARARG as u8) {
            unsafe { std::mem::transmute(value) }
        } else {
            println!("invalid opcode? {}", value);
            Opcode::INVALID
        }

    }
}

pub trait InstructionDecode {
    type Unpack: Unpacker;
}

pub trait Unpacker {
    type Unpacked;
    #[inline(always)]
    fn unpack(inst: InstBits) -> Self::Unpacked;
}

pub struct AB;
impl Unpacker for AB {
    type Unpacked = (u8, u16); // A: 8, B: 9
    fn unpack(inst: InstBits) -> Self::Unpacked {
        (inst.A() as u8, inst.B() as u16)
    }
}

pub struct ABx;
impl Unpacker for ABx {
    type Unpacked = (u8, u32); // A: 8, Bx: 18
    fn unpack(inst: InstBits) -> Self::Unpacked {
        (inst.A() as u8, inst.Bx() as u32)
    }
}

pub struct ABC;
impl Unpacker for ABC {
    type Unpacked = (u8, u16, u16); // A: 8, B: 9, C: 9
    fn unpack(inst: InstBits) -> Self::Unpacked {
        (inst.A() as u8, inst.B() as u16, inst.C() as u16)
    }
}

pub struct sBx;
impl Unpacker for sBx {
    type Unpacked = i32; // A: 8, B: 9, C: 9
    fn unpack(inst: InstBits) -> Self::Unpacked {
        // 131071 = 2^18-1 >> 1, aka half the bias
        (Wrapping(inst.Bx()) - Wrapping(131071)).0 as i32
    }
}

pub struct AsBx;
impl Unpacker for AsBx {
    type Unpacked = (u8, i32); // A: 8, sBx: 18
    fn unpack(inst: InstBits) -> Self::Unpacked {
        // 131071 = 2^18-1 >> 1, aka half the bias
        (inst.A() as u8, (inst.Bx() as isize - 131071) as i32)
    }
}


struct MOVE;
impl InstructionDecode for MOVE { type Unpack = AB; }

struct LOADNIL;
impl InstructionDecode for LOADNIL { type Unpack = AB; }

struct LOADBOOL;
impl InstructionDecode for LOADBOOL { type Unpack = ABC; }

struct GETUPVAL;
impl InstructionDecode for GETUPVAL{ type Unpack = AB; }

struct SETUPVAL;
impl InstructionDecode for SETUPVAL{ type Unpack = AB; }

struct LOADK;
impl InstructionDecode for LOADK { type Unpack = ABx; }

struct RETURN;
impl InstructionDecode for RETURN { type Unpack = AB; }

struct CLOSURE;
impl InstructionDecode for CLOSURE { type Unpack = ABx; }

struct GETGLOBAL;
impl InstructionDecode for GETGLOBAL { type Unpack = ABx; }

struct SETGLOBAL;
impl InstructionDecode for SETGLOBAL { type Unpack = ABx; }

struct CALL;
impl InstructionDecode for CALL { type Unpack = ABC; }

struct TEST;
impl InstructionDecode for TEST { type Unpack = ABC; }

struct EQ;
impl InstructionDecode for EQ { type Unpack = ABC; }

struct JMP;
impl InstructionDecode for JMP { type Unpack = sBx; }

struct NEWTABLE;
impl InstructionDecode for NEWTABLE { type Unpack = ABC; }

struct SELF;
impl InstructionDecode for SELF { type Unpack = ABC; }

struct GETTABLE;
impl InstructionDecode for GETTABLE { type Unpack = ABC; }

struct SETTABLE;
impl InstructionDecode for SETTABLE { type Unpack = ABC; }

struct SETLIST;
impl InstructionDecode for SETLIST { type Unpack = ABC; }

struct FORPREP;
impl InstructionDecode for FORPREP { type Unpack = AsBx; }

struct FORLOOP;
impl InstructionDecode for FORLOOP { type Unpack = AsBx; }

struct LEN;
impl InstructionDecode for LEN { type Unpack = AB; }

struct CONCAT;
impl InstructionDecode for CONCAT { type Unpack = ABC; }

struct UNM;
impl InstructionDecode for UNM { type Unpack = AB; }


#[derive(Debug, PartialEq, Eq, PartialOrd, Hash)]
pub struct FakeRc<T> {
    val: std::ptr::NonNull<T>,
}

impl<T> FakeRc<T> {
    pub fn new(val: T) -> Self {
        let bo = Box::leak(Box::new(val));
        let bo_ptr = std::ptr::NonNull::from(bo);
        Self { val: bo_ptr }
    }
    fn as_ptr(val: &Self) -> *const T {
        val.val.as_ptr()
    }
}

impl<T> Deref for FakeRc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // safety: just trust me bro
        unsafe { self.val.as_ref() }
    }
}

impl<T> Clone for FakeRc<T> {
    fn clone(&self) -> Self {
        Self { val: self.val.clone() }
    }
}

// For testing RC overhead
#[cfg(feature = "skip_rc")]
pub type Rc<T> = FakeRc<T>;
#[cfg(not(feature = "skip_rc"))]
pub use std::rc::Rc;

// For testing Vec bounds checking overhead
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Hash)]
pub struct UnsafeVec<T> {
    vec: Vec<T>,
}

impl<T> From<Vec<T>> for UnsafeVec<T> {
    fn from(value: Vec<T>) -> Self {
        UnsafeVec { vec: value }
    }
}

impl<T> Deref for UnsafeVec<T> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.vec
    }
}

impl<T> DerefMut for UnsafeVec<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.vec
    }
}


impl<T> IntoIterator for UnsafeVec<T> {
    type Item = T;

    type IntoIter = <Vec<T> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.vec.into_iter()
    }
}

impl<T, Idx: std::slice::SliceIndex<[T]>> Index<Idx> for UnsafeVec<T> {
    type Output = Idx::Output;

    fn index(&self, index: Idx) -> &Self::Output {
        // safety: haha
        unsafe { self.vec.get_unchecked(index) }
    }
}

impl<T, Idx: std::slice::SliceIndex<[T]>> IndexMut<Idx> for UnsafeVec<T> {
    fn index_mut(&mut self, index: Idx) -> &mut <Self as Index<Idx>>::Output {
        // safety: smile emoji
        unsafe { self.vec.get_unchecked_mut(index) }
    }
}

impl<T: Mark> Mark for UnsafeVec<T> {
    fn mark(&self, owner: &Owner) {
        self.vec.mark(owner)
    }
}

#[cfg(feature = "skip_vec")]
pub type FVec<T> = UnsafeVec<T>;
#[cfg(not(feature = "skip_vec"))]
pub type FVec<T> = Vec<T>;

pub struct Tc<T>(pub Gc<TLCell<TlcOwner, T>>);

impl<T> Debug for Tc<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "tc({:p})", self.0.as_ptr())
    }
}

impl<T> PartialEq for Tc<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0.as_ptr() == other.0.as_ptr()
    }
}

impl<T> Eq for Tc<T> { }

impl<T> Hash for Tc<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_usize(self.0.as_ptr() as usize)
    }
}

impl<T> Tc<T> {
    pub fn new(val: T) -> Self {
        Self(Gc::new(TLCell::new(val)))
    }

    pub fn as_ptr(&self) -> *const () {
        self.0.as_ptr().cast()
    }

}

impl<T: Mark> Tc<T> {
    /// Replace the whole cell contents, firing the write barrier first. Fusing the two is
    /// the misuse-resistant way to store into a non-table `Tc` (upvalue cells) — prefer it
    /// over `*tc.rw(owner) = value`. See Note [Write barriers].
    #[inline]
    pub fn replace(&self, owner: &mut Owner, value: T) {
        self.0.write_barrier(&value, owner);
        *self.0.deref().rw(owner) = value;
    }
}

impl<T> Clone for Tc<T> {
    fn clone(&self) -> Self {
        Tc(self.0.clone())
    }
}

impl<T> Deref for Tc<T> {
    type Target = TLCell<TlcOwner, T>;

    fn deref(&self) -> &Self::Target {
        self.0.deref()
    }
}

#[derive(Default)]
pub struct InternedHasher {
    hasher: FxBuildHasher,
}

// A plain `FxBuildHasher` wrapper; the interned-string precomputed-hash
// optimization lives in `LCanon`'s `Hash` impl.
impl std::hash::BuildHasher for InternedHasher {
    type Hasher = <FxBuildHasher as BuildHasher>::Hasher;

    fn build_hasher(&self) -> Self::Hasher {
        self.hasher.build_hasher()
    }
}

// Values are raw `LBoxed`; hash keys are `LCanon`. See Note [Canonical values].
#[derive(Debug)]
pub struct Table<'src, 'intern> {
    pub array: FVec<LBoxed<'src, 'intern>>,
    /// Inserted into and cleared only through `insert_hash` and `clear_hash`,
    /// which count the global environment's entry moves.
    pub hash: IndexMap<LCanon<'src, 'intern>, LBoxed<'src, 'intern>, InternedHasher>,
    pub epoch: usize,
    /// Whether this is the global environment. See Note [Global caches] in
    /// `generator`.
    pub environment: bool,
}

thread_local! {
    /// How many times the global environment's hash entries have moved: global
    /// caches holding an entry's address are valid while it's unchanged. See
    /// Note [Global caches] in `generator`.
    static ENV_MOVES: Cell<u64> = const { Cell::new(0) };
}

/// See `ENV_MOVES`.
pub fn env_moves() -> u64 {
    ENV_MOVES.with(|moves| moves.get())
}

impl<'src, 'intern> Table<'src, 'intern> {
    pub fn new(array: usize, hash: usize) -> Self {
        Self {
            array: vec![LBoxed::NIL; array].into(),
            hash: IndexMap::with_capacity_and_hasher(hash, InternedHasher::default()),
            epoch: 0,
            environment: false,
        }
    }

    /// Insert into the hash part. A new key may reallocate the entries, moving
    /// them. Returns the key's old value.
    pub fn insert_hash(&mut self, key: LCanon<'src, 'intern>, value: LBoxed<'src, 'intern>) -> Option<LBoxed<'src, 'intern>> {
        let old = self.hash.insert(key, value);
        if old.is_none() && self.environment {
            ENV_MOVES.with(|moves| moves.set(moves.get() + 1));
        }
        old
    }

    /// Empty the hash part, moving every entry out.
    pub fn clear_hash(&mut self) {
        self.hash.clear();
        if self.environment {
            ENV_MOVES.with(|moves| moves.set(moves.get() + 1));
        }
    }

    /// Insert a key/value without an intern arena to canonicalize the key (unlike
    /// `set`/`get`). Valid only for builtin keys, which are already interned strings
    /// and so satisfy the canonical-form invariant of Note [Canonical values] directly.
    pub fn insert_lvalue(&mut self, key: LValue<'src, 'intern>, value: LValue<'src, 'intern>) {
        self.insert_hash(LCanon(LBoxed::box_lvalue(key)), LBoxed::box_lvalue(value));
        self.epoch += 1;
    }
}

/// The array slot of a number key: the array part holds the integer keys from
/// 1 up (growing to fit on a write), the hash part every other number (zero,
/// negatives, fractions), as Lua keeps them apart.
/// Lua's `%`: `a - floor(a / b) * b`, taking the sign of `b` where Rust's `%`
/// takes the sign of `a`.
#[inline(always)]
pub fn lua_mod(a: f64, b: f64) -> f64 {
    a - (a / b).floor() * b
}

pub(crate) fn array_slot(n: f64) -> Option<usize> {
    (n >= 1.0 && n.fract() == 0.0 && n <= u32::MAX as f64).then(|| n as usize - 1)
}

impl<'src, 'intern> Tc<Table<'src, 'intern>> {
    /// Fire the table write barrier before mutating this table's array/hash in place.
    /// See Note [Write barriers].
    #[inline]
    pub fn barrier_back(&self) {
        // Nothing is black outside a collection cycle. See Note [Write barriers].
        debug_assert!(crate::gc::gc_in_progress() || !self.0.is_black(), "a black table outside a collection cycle");
        if crate::gc::gc_in_progress() {
            self.0.backward_barrier();
        }
    }

    /// Look up a key. Numbers index the array part; everything else goes through
    /// the hash part as an `LCanon`. See Note [Canonical values].
    #[inline]
    pub fn get(&self, owner: &Owner, key: &LBoxed<'src, 'intern>, intern: &'intern internment::Arena<IStr<'src>>) -> Option<LBoxed<'src, 'intern>> {
        if let Some(slot) = key.as_number().and_then(array_slot) {
            return Some(self.ro(owner).array.get(slot).copied().unwrap_or(LBoxed::NIL));
        }
        let k = LCanon::new(*key, intern);
        self.ro(owner).hash.get(&k).copied()
    }

    #[inline]
    pub fn set(&mut self, owner: &mut Owner, key: LBoxed<'src, 'intern>, value: LBoxed<'src, 'intern>, intern: &'intern internment::Arena<IStr<'src>>) {
        self.barrier_back();
        if let Some(slot) = key.as_number().and_then(array_slot) {
            // TODO: sparse arrays
            if self.rw(owner).array.len() <= slot {
                self.rw(owner).array.resize_with(slot + 1, || LBoxed::NIL);
            }
            self.rw(owner).array[slot] = value;
            return;
        }
        let k = LCanon::new(key, intern);
        self.rw(owner).insert_hash(k, value);
        self.rw(owner).epoch += 1;
    }
}

#[repr(u8)]
#[derive(Hash, Clone)]
pub enum InternString<'intern, 'src> {
    Interned(ArenaIntern<'intern, IStr<'src>>),
    Owned(Gc<LStr>),
}

impl<'intern, 'src> PartialEq for InternString<'intern, 'src> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (InternString::Interned(self_s), InternString::Interned(other_s)) => {
                if self_s.deref().as_bytes().as_ptr() == other_s.deref().as_bytes().as_ptr() {
                    return true
                } else {
                    return self_s == other_s
                }
            },
            (InternString::Interned(inter), InternString::Owned(own)) |
            (InternString::Owned(own), InternString::Interned(inter)) => {
                inter.deref().as_bytes() == own.as_slice()
            },
            (InternString::Owned(self_o), InternString::Owned(other_o)) => {
                self_o == other_o
            }
        }
    }
}

impl<'intern, 'src> PartialOrd for InternString<'intern, 'src> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (InternString::Interned(self_s), InternString::Interned(other_s)) => {
                if self_s.deref().as_bytes().as_ptr() == other_s.deref().as_bytes().as_ptr() {
                    self_s.partial_cmp(self_s)
                } else {
                    self_s.partial_cmp(other_s)
                }
            },
            (InternString::Interned(inter), InternString::Owned(own)) |
            (InternString::Owned(own), InternString::Interned(inter)) => {
                inter.as_bytes().partial_cmp(own.as_slice())
            },
            (InternString::Owned(self_o), InternString::Owned(other_o)) => {
                self_o.as_slice().partial_cmp(other_o.as_slice())
            }
        }
    }
}

impl<'intern, 'src> Eq for InternString<'intern, 'src> { }

impl<'intern, 'src> Debug for InternString<'intern, 'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InternString::Interned(i) => write!(f, "{}", String::from_utf8_lossy(i.as_bytes())),
            InternString::Owned(o) => write!(f, "{}", String::from_utf8_lossy(o.as_slice())),
        }
    }
}

impl<'intern, 'src> InternString<'intern, 'src> {
    pub fn intern<S: Into<String>>(intern: &'intern internment::Arena<IStr<'src>>, s: S) -> LValue<'src, 'intern> {
        let bytes: Vec<u8> = s.into().into_bytes();
        use std::hash::BuildHasher;
        let hash = FxBuildHasher::default().hash_one(bytes.as_slice());
        debug!("interning hash {} for {:?}", hash, bytes);
        LValue::InternedString(intern.intern(IStr { kind: LBoxed::KIND_INTERNED, bytes: Cow::Owned(bytes), hash }))
    }
}

impl<'intern, 'src> Deref for InternString<'intern, 'src> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        match self {
            InternString::Interned(i) => i.deref().as_bytes(),
            InternString::Owned(o) => o.as_slice(),
        }
    }
}

#[repr(u8)]
#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub enum LValue<'src, 'intern> {
    Nil = 0,
    Bool(bool) = 1,
    Number(Number) = 2,
    Table(Tc<Table<'src, 'intern>>) = 3,
    // Shared variants get mapped so they have a bit we can check
    // Strings
    InternedString(ArenaIntern<'intern, IStr<'src>>) = 4,
    // Strings are immutable, so owned strings need no interior mutability: a
    // plain `Gc<LStr>` (not `Tc`) lets their bytes be read without an
    // `owner`, which is what makes content-based equality/hashing possible.
    OwnedString(Gc<LStr>) = 5,
    // Closures
    LClosure(Tc<LClosure<'src, 'intern>>) = 8,
    NClosure(NClosure) = 9,
}

/// The NuN-boxed value type lives in its own module so its payload field can
/// stay private (see `lboxed`), which is what makes `LBoxed::unbox` safe.
pub use crate::lboxed::LBoxed;
use crate::lboxed::NClosureCell;
pub use crate::lboxed::IStr;

/// Intern raw bytes into the arena, returning the canonical handle. The bytes are
/// owned by the record (`Cow::Owned`), so the arena frees a deduped duplicate; it
/// dedups by content, so equal bytes always yield the same handle.
pub fn intern_bytes<'src, 'intern>(
    intern: &'intern internment::Arena<IStr<'src>>,
    bytes: &[u8],
) -> ArenaIntern<'intern, IStr<'src>> {
    use std::hash::BuildHasher;
    let hash = FxBuildHasher::default().hash_one(bytes);
    intern.intern(IStr { kind: LBoxed::KIND_INTERNED, bytes: Cow::Owned(bytes.to_vec()), hash })
}

// Stamp the offset-0 `kind` header of each heap cell at allocation time, so a
// raw untagged pointer can recover its type. Non-cell allocations use the
// blanket default (0) from gc::CellKind. (NClosures are leaked, not GC'd, and
// stamp their header directly in `box_lvalue`.)
impl<'src, 'intern> crate::gc::CellKind for TLCell<TlcOwner, Table<'src, 'intern>> {
    fn cell_kind() -> u8 { LBoxed::KIND_TABLE }
}
impl<'src, 'intern> crate::gc::CellKind for TLCell<TlcOwner, LClosure<'src, 'intern>> {
    fn cell_kind() -> u8 { LBoxed::KIND_LCLOSURE }
}
impl crate::gc::CellKind for LStr {
    fn cell_kind() -> u8 { LBoxed::KIND_OWNED }
}

// Note [Canonical values]
// ~~~~~~~~~~~~~~~~~~~~~~~~~
// `LCanon` is an `LBoxed` in canonical form: equal values have identical bits, so it
// implements `Hash`/`Eq` by value — comparing the raw bits, pointers included — with no
// `owner`. `LCanon::new` does the canonicalizing: an owned string is interned, which the
// arena dedups to the one pointer shared by every string with those bytes, and a number
// is boxed canonically (`LBoxed::from_number`), as an integer and the equal double are
// one key (Note [Integer encoding] in `lboxed`), as are 0 and -0. Everything else is
// already canonical: interned strings are that unique pointer, tables/closures compare
// by identity, and bool/nil are their own bits.
//
// Hashing agrees with that equality: an interned string hashes by its precomputed content
// hash (so strings spread by content, not by arena address), everything else by its bits.
// Equal bits give equal hashes.
/// An `LBoxed` in canonical form, giving owner-free `Hash`/`Eq`. See Note [Canonical values].
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LCanon<'src, 'intern>(LBoxed<'src, 'intern>);

impl<'src, 'intern> LCanon<'src, 'intern> {
    /// Canonicalize an `LBoxed`; see Note [Canonical values]. `unbox` is
    /// `inline(always)` and this matches a single variant, so it folds to one
    /// header-tag check (cf. `as_table`).
    #[inline(always)]
    pub fn new(v: LBoxed<'src, 'intern>, intern: &'intern internment::Arena<IStr<'src>>) -> Self {
        match v.unbox() {
            LValue::OwnedString(g) => LCanon(LBoxed::interned(intern_bytes(intern, g.as_slice()))),
            LValue::Number(n) => Self::number(n.0),
            _ => LCanon(v),
        }
    }

    /// A number key, -0 as 0. See Note [Canonical values].
    #[inline(always)]
    fn number(n: f64) -> Self {
        LCanon(LBoxed::from_number(if n == 0.0 { 0.0 } else { n }))
    }

    #[inline(always)]
    /// A constant: string constants are interned already.
    pub fn constant(k: &LConstant<'src, 'intern>) -> Self {
        match k {
            Constant::Number(n) => Self::number(n.0),
            k => LCanon(LBoxed::from(k)),
        }
    }

    pub fn boxed(self) -> LBoxed<'src, 'intern> {
        self.0
    }
}

// Equality and hashing per Note [Canonical values].
impl PartialEq for LCanon<'_, '_> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.0.bits() == other.0.bits()
    }
}
impl Eq for LCanon<'_, '_> {}

impl Hash for LCanon<'_, '_> {
    #[inline(always)]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self.boxed().unbox() {
            LValue::InternedString(i) => state.write_u64(i.hash),
            _ => state.write_u64(self.0.bits()),
        }
    }
}

impl Debug for LCanon<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LType {
    Unknown,
    Nil,
    Bool,
    Number,
    String,
    Closure,
    Table,
}

impl std::fmt::Display for LType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LType::Unknown => write!(f, "?"),
            LType::Nil => write!(f, "nil"),
            LType::Bool => write!(f, "bool"),
            LType::Number => write!(f, "number"),
            LType::String => write!(f, "string"),
            LType::Closure => write!(f, "func"),
            LType::Table => write!(f, "table"),
        }
    }
}

impl<'src, 'intern> LValue<'src, 'intern> {
    pub fn compare(&self, opcode: Opcode, right: Self, owner: &Owner) -> Result<bool, String> {
        // TODO: metamethods
        if std::mem::discriminant(self) != std::mem::discriminant(&right) {
            panic!("bad compare");
        }
        match (self, &right) {
            (LValue::Nil, LValue::Nil) => {
                return Err("attempt to compare nil".into())
            },
            (LValue::Table(left_tab), LValue::Table(right_tab)) => {
                unimplemented!("metamethod")
            },
            (LValue::LClosure(left_c), LValue::LClosure(right_c)) => {
                return Err("attempt to compare functions".into())
            },
            (LValue::NClosure(left_c), LValue::NClosure(right_c)) => {
                return Err("attempt to compare functions".into())
            },
            _ => (),
        }

        match opcode {
            Opcode::EQ => {
                Ok(*self == right)
            },
            Opcode::LT => {
                match (self, &right) {
                    (LValue::Bool(left_b), LValue::Bool(right_b)) => Ok(left_b < right_b),
                    (LValue::Number(left_n), LValue::Number(right_n)) => Ok(left_n < right_n),
                    (LValue::InternedString(left_s), LValue::InternedString(right_s)) =>
                        Ok(left_s.as_bytes() < right_s.as_bytes()),
                    (LValue::OwnedString(left_s), LValue::OwnedString(right_s)) =>
                        Ok(left_s.as_slice() < right_s.as_slice()),
                    _ => panic!()
                }
            },
            Opcode::LE => {
                match (self, &right) {
                    (LValue::Bool(left_b), LValue::Bool(right_b)) => Ok(left_b <= right_b),
                    (LValue::Number(left_n), LValue::Number(right_n)) => Ok(left_n <= right_n),
                    (LValue::InternedString(left_s), LValue::InternedString(right_s)) =>
                        Ok(left_s.as_bytes() <= right_s.as_bytes()),
                    _ => panic!()
                }

            },
            _ => panic!()
        }
    }

    #[inline(always)]
    pub fn numeric_op(&self, opcode: Opcode, right: &Self) -> Result<LValue<'src, 'intern>, String> {
        match (self, right) {
            (LValue::Number(left_n), LValue::Number(right_n)) => {
                match opcode {
                    Opcode::ADD =>
                        Ok(LValue::Number(Number(left_n.0 + right_n.0))),
                    Opcode::SUB =>
                        Ok(LValue::Number(Number(left_n.0 - right_n.0))),
                    Opcode::MUL =>
                        Ok(LValue::Number(Number(left_n.0 * right_n.0))),
                    Opcode::DIV =>
                        Ok(LValue::Number(Number(left_n.0 / right_n.0))),
                    Opcode::MOD =>
                        Ok(LValue::Number(Number(lua_mod(left_n.0, right_n.0)))),
                    Opcode::POW =>
                        Ok(LValue::Number(Number(left_n.0.powf(right_n.0)))),
                    _ => unsafe { std::hint::unreachable_unchecked() },
                }
            },
            // TODO: metamethods and errors
            _ => unimplemented!(),
        }
    }

    pub fn len(&self, owner: &Owner) -> Result<LValue<'src, 'intern>, String> {
        // TODO: metamethods
        match self {
            LValue::InternedString(s) => Ok(LValue::Number(Number(s.as_bytes().len() as _))),
            LValue::OwnedString(s) => Ok(LValue::Number(Number(s.len() as _))),
            LValue::Table(t) => {
                // TODO: sparse arrays
                Ok(LValue::Number(Number(t.ro(owner).array.len() as _)))
            },
            _ => unimplemented!(),
        }
    }

    pub fn as_bool(&self, owner: &Owner) -> Result<LValue<'src, 'intern>, String> {
        match self {
            LValue::Bool(b) => Ok(self.clone()),
            LValue::Nil => Ok(LValue::Bool(false)),
            _ => Ok(LValue::Bool(true)),
        }
    }

    pub fn as_string(&self, owner: &Owner) -> Option<Gc<LStr>> {
        match self {
            LValue::OwnedString(s) => Some(s.clone()),
            value => Some(Gc::string(&value.string_bytes(owner))),
        }
    }

    /// The bytes `tostring` gives a value.
    pub fn string_bytes(&self, owner: &Owner) -> Vec<u8> {
        // TODO: metamethods?
        let mut s = vec![];
        match self {
            LValue::OwnedString(g) => s.extend_from_slice(g.as_slice()),
            LValue::InternedString(i) => s.extend_from_slice(i.as_bytes()),
            LValue::Number(f) => { write!(s, "{}", f.0); },
            LValue::Table(tc) => { write!(s, "{:?}", tc); },
            LValue::Nil => { write!(s, "nil"); },
            LValue::Bool(b) => { write!(s, "{b}"); },
            LValue::LClosure(l) => {
                let line = unsafe { (*l.0.ro(owner).prototype).line_defined };
                let src = unsafe { &(*l.0.ro(owner).prototype).source };
                write!(s, "function({:p}, {:?} @ {})", l.as_ptr(), src, line);
            },
            LValue::NClosure(nf) => { write!(s, "native({:p})", nf.native()); },
        }
        s
    }

    pub fn as_string_nolock(&self) -> Option<Gc<LStr>> {
        // TODO: metamethods?
        let mut s = vec![];
        match self {
            LValue::OwnedString(g) => return Some(g.clone()),
            LValue::InternedString(i) => s.extend_from_slice(i.as_bytes()),
            LValue::Number(f) => { write!(s, "{}", f.0); },
            LValue::Table(tc) => { write!(s, "{:?}", tc); },
            LValue::Nil => return None,
            LValue::LClosure(l) => { write!(s, "function({:p})", l.as_ptr()); },
            x => unimplemented!("{:?}", x),
        }
        Some(Gc::string(&s))
    }

    pub fn gettable(&self, owner: &mut Owner, index: Cow<'_, LValue<'src, 'intern>>, intern: &'intern internment::Arena<IStr<'src>>) -> LValue<'src, 'intern> {
        let val_b = match self {
            LValue::Table(tab) => {
                debug!("table {:?}", tab);
                let key = LBoxed::box_lvalue(index.into_owned());
                tab.get(owner, &key, intern).map(|b| b.unbox()).unwrap_or(LValue::Nil)
            },
            x => unimplemented!("gettable on {:?}", x),
        };
        debug!("gettable {:?}", &val_b);
        return val_b;
    }
}

impl<'src, 'intern> From<&LConstant<'src, 'intern>> for LValue<'src, 'intern>
{
    #[inline]
    fn from(value: &LConstant<'src, 'intern>) -> Self {
        match value {
            Constant::Nil => LValue::Nil,
            Constant::Bool(b) => LValue::Bool(*b),
            Constant::Number(i) => LValue::Number(*i),
            Constant::String(s) => LValue::InternedString(s.clone()),
        }
    }
}

impl<'src, 'intern> PartialOrd for LConstant<'src, 'intern> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub enum Upvalue<'src, 'intern> {
    Open(usize), // stack index
    Closed(Tc<LBoxed<'src, 'intern>>),
}

pub type LProto<'src, 'intern> = *const FunctionBlock<'src, LConstant<'src, 'intern>>;
pub struct LClosure<'src, 'intern> {
    pub prototype: LProto<'src, 'intern>,
    //environment: LTable<'src>,
    pub upvalues: FVec<Tc<Upvalue<'src, 'intern>>>,
}

impl<'src, 'intern> Debug for LClosure<'src, 'intern> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "closure(upvalues={:?})", self.upvalues)
    }
}

/// A native function: from its arguments, it writes its results into the slots
/// for them (which overlap the arguments; see Note [Library natives] in
/// `library`), and returns how many it wrote.
pub type NativeFunc = for<'id, 'a, 'src, 'intern> fn(LCellOwner<'id>, &'a LCell<'id, [LBoxed<'src, 'intern>]>, &'a LCell<'id, [LBoxed<'src, 'intern>]>, &mut Owner) -> usize;
/// A native's window op for a call to it (the `CALL`'s `a`, `b`, `c`), with
/// which of its arguments are in the integer encoding (`ints`), if it has one
/// for that call's arity. See Note [Native windows] in `library`.
pub type NativeWindow = fn(a: usize, b: u16, c: u16, ints: &[bool]) -> Option<NativeOp>;

/// A call to a native run as a window op: the op, the type every argument must
/// have for it (the op assumes it), and its result's type.
pub struct NativeOp {
    pub window: std::rc::Rc<dyn crate::window::Window>,
    pub args: LType,
    pub result: crate::generator::CType,
}

#[derive(Clone, Copy)]
pub struct NClosure {
    // A `'static`, non-GC cell (leaked at `new`) whose pointer is the native's
    // boxed form; the JIT reads `native` through it. See `lboxed::NClosureCell`.
    pub(crate) cell: &'static NClosureCell,
}

impl PartialEq for NClosure {
    fn eq(&self, other: &Self) -> bool {
        core::ptr::fn_addr_eq(self.native(), other.native())
    }
}

impl Eq for NClosure { }

impl Hash for NClosure {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.native().hash(state);
    }
}

impl<'src> Debug for NClosure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<native function {:p}>", self.native())
    }
}

impl<'src, 'intern> LClosure<'src, 'intern> {
    pub fn new(prototype: LProto<'src, 'intern>) -> Self {
        Self {
            prototype,
            upvalues: vec![].into(),
        }
    }
}

#[repr(u8)]
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Closure<'src, 'intern> {
    Lua(Tc<LClosure<'src, 'intern>>),
    Native(NClosure),
}

impl NClosure {
    pub fn new(native: NativeFunc) -> Self {
        NClosure { cell: NClosureCell::leak(native) }
    }

    /// A native that runs as a window op where `window` gives one.
    pub fn windowed(native: NativeFunc, window: NativeWindow) -> Self {
        NClosure { cell: NClosureCell::leak_windowed(native, window) }
    }

    /// The window op a call `a`, `b`, `c` to this native runs as, if any.
    pub fn window(&self, a: usize, b: u16, c: u16, ints: &[bool]) -> Option<NativeOp> {
        self.cell.window.and_then(|window| window(a, b, c, ints))
    }

    pub fn native(&self) -> NativeFunc {
        self.cell.native
    }

    pub fn get_ptr(&self) -> *const () {
        self.native() as _
    }
}

pub struct Vm<'src, 'intern> {
    // This is terrible, but because we reference FunctionBlocks in Gc<T> types,
    // we can't use proper lifetimes for it: Rust doesn't know that a Gc<T> won't
    // stick around past 'src
    pub top_level: LProto<'src, 'intern>,
}

/// Branded view of a VM and its arena inside a [`Vm::scope`], at a fresh invariant `'gc`. The
/// brand confines GC values to the scope. See Note [Scoped heap].
pub struct Scoped<'gc> {
    // `*const Vm<'src,'intern>` / `*const Arena<..'src..>`, type-erased and read back at `'gc`.
    vm: *const (),
    intern: *const (),
    // The scope's rooting token; its `'gc` makes `Scoped` invariant (which pins the brand — see
    // the SAFETY note on `Vm::scope`) and unlocks the crate-private `Vm::run`/`global_env`.
    gc: GcCtx<'gc>,
}

impl<'gc> Scoped<'gc> {
    /// The VM at the scope brand; every GC value it returns is `<'gc,'gc>`.
    #[inline]
    pub fn vm(&self) -> &'gc Vm<'gc, 'gc> {
        // SAFETY: narrowing a `&Vm` whose `'src`/`'intern` outlive `'gc` down to `'gc`. See the
        // SAFETY note on `Vm::scope`.
        unsafe { &*(self.vm as *const Vm<'gc, 'gc>) }
    }

    /// The interning arena at the scope brand, for `InternString::intern`.
    #[inline]
    pub fn intern(&self) -> &'gc internment::Arena<IStr<'gc>> {
        // SAFETY: as `vm`.
        unsafe { &*(self.intern as *const internment::Arena<IStr<'gc>>) }
    }

    /// Build the global environment table. Scope-gated; see Note [Scoped heap].
    #[inline]
    pub fn global_env(&self) -> Tc<Table<'gc, 'gc>> {
        self.vm().global_env(self.intern())
    }

    /// Run a closure — the only way in, since `Vm::run` is crate-private. See Note [Scoped
    /// heap].
    #[inline]
    pub fn run(
        &self,
        owner: &mut Owner,
        _G: Tc<Table<'gc, 'gc>>,
        clos: Tc<LClosure<'gc, 'gc>>,
        args: ValueStack<'gc, 'gc>,
    ) -> Result<FVec<LValue<'gc, 'gc>>, Box<dyn Error>> {
        self.vm().run(self.gc, owner, _G, clos, args, self.intern())
    }
}

thread_local! {
    /// Set while a [`Vm::scope`] is active; enforces non-re-entrancy. See Note [Scoped heap].
    static IN_SCOPE: Cell<bool> = const { Cell::new(false) };
}

/// RAII latch for [`Vm::scope`] non-re-entrancy; clears the flag on scope exit.
struct ScopeGuard;
impl ScopeGuard {
    fn enter() -> Self {
        IN_SCOPE.with(|f| {
            assert!(!f.get(), "Vm::scope is not re-entrant: a GC scope is already active on this thread");
            f.set(true);
        });
        ScopeGuard
    }
}
impl Drop for ScopeGuard {
    fn drop(&mut self) { IN_SCOPE.with(|f| f.set(false)); }
}

/// Where a call returns to: a specializer block and the offset of the residual after the
/// call in it.
#[derive(Debug)]
pub struct ReturnLocation(pub BlockId, pub usize);

/// A [`ReturnLocation`] packed into a single register-sized word (see
/// [`ReturnLocation::pack`]). `#[repr(transparent)]` over `usize`, so it crosses the
/// JIT/`extern "C"` boundary in one register.
#[derive(Debug, Clone, Copy)]
#[repr(transparent)]
pub struct PackedLocation(usize);

impl PackedLocation {
    /// The raw word, for the JIT to load into an argument register.
    #[inline(always)]
    pub fn bits(self) -> usize {
        self.0
    }
}

impl ReturnLocation {
    /// Pack into a `PackedLocation` so it can cross the JIT/`extern "C"` boundary
    /// without passing a `repr(Rust)` struct by value: `(off << 32) | block`, the
    /// layout the JIT's `lua_return` uses for its return encoding.
    pub fn pack(self) -> PackedLocation {
        let ReturnLocation(BlockId(block), off) = self;
        PackedLocation((off << 32) | block)
    }

    pub fn unpack(p: PackedLocation) -> Self {
        ReturnLocation(BlockId(p.0 & 0xffff_ffff), p.0 >> 32)
    }
}

// Note [Stack frames]
// ~~~~~~~~~~~~~~~~~~~~
// A call frame occupies a contiguous span of the register file (`vals`) starting at
// `base`; `RunState::top` is its dynamic Lua top (the variable-count-span cursor).
// `call_lua` grows `vals` to fit the callee's `max_stack` and records the caller's
// state in a `CallstackEntry`; `do_return` pops it and restores that state.
//
// The GC marks `0..vals.len()`, so `do_return` shrinks `vals` back down as frames pop,
// or dead frames would be marked forever. The bound it must never cross is
// `RunState::natural_max` = `max` over all *live* frames of `base_i + max_stack_i`:
// truncating below that would strip registers a suspended outer frame still reads. A
// per-frame `base + max_stack` is only one term of that max (a shallow callee nested
// in a deeper stack sits below it), so it can't be used directly.
//
// `natural_max` follows call/return stack discipline: `call_lua` saves it as the
// callee's `limit`, then grows it by the callee's frame; `do_return` restores it from
// `limit` and truncates `vals` to it.
//
// MULTRET results are the one thing that can sit *above* `natural_max`: a call
// returning a variable count writes them from `rloc` up to `rloc + r_count`, which can
// overshoot the caller's frame, so `do_return` truncates to `limit.max(rloc +
// r_count)` to keep them. That overshoot is deliberately *not* recorded as any later
// frame's `limit` (a `limit` is always a `natural_max`), so a subsequent return
// truncates it away — and that is sound, not a leak of live data, because of a Lua
// guarantee:
//
//   A multi-value expression is only ever consumed *in place* — as the trailing
//   arguments of a call, the trailing items of a table constructor, or a function's
//   return list. Lua has no syntax to bind the whole list to a name or to read it
//   after an intervening call; `local a = f()` keeps only the first value.
//
// So consider `foo` doing `t = {multiret()}` (which inflates `vals` with the results
// above foo's frame) and then calling `bar()`. By the time `bar` is called the results
// have already been consumed by the `{...}` and are unreachable — nothing in `foo` can
// name them across the `bar()` call. Hence `bar`'s return truncating `vals` back to
// foo's `natural_max` cannot drop anything `foo` still uses; it just reclaims the dead
// overshoot, which is what stops it lingering (and being GC-marked) for the rest of
// foo's execution.
#[derive(Debug)]
pub struct CallstackEntry<'src, 'intern> { pub clos: Tc<LClosure<'src, 'intern>>, pub ret: ReturnLocation, pub frame: usize, pub limit: usize, pub witness_frame: usize, pub witness_top: usize, pub rloc: usize, pub c: u16 }

/// Where a frame's hash key was found in its table's hash part (its entry's
/// index, and its value's address), and the table's epoch then. See Note
/// [Hash witnesses].
#[derive(Debug, Clone, Copy)]
pub struct HashWitness {
    pub index: usize,
    pub value: *mut LBoxed<'static, 'static>,
    pub epoch: usize,
}

impl Default for HashWitness {
    fn default() -> Self {
        HashWitness { index: 0, value: core::ptr::null_mut(), epoch: 0 }
    }
}

// Note [Hash witnesses]
// ~~~~~~~~~~~~~~~~~~~~~
// A frame's hash witnesses are the region of `hash_witnesses` from its
// `witness_base` up; a call's region starts at the caller's `witness_top`,
// which `href_init` raises past each witness it writes, and a return resets it.
// The vector itself never shrinks, so a call never refills it: entries above
// `witness_top` are stale, but no frame reads one it hasn't written, as a
// function's entry context has no hash keys and a hash key's `href_init` runs
// before any use of it.
//
// A witness holds its entry's index and its value's address while the table's
// epoch is the one it saw: a table's hash part only reallocates or moves an
// entry when a key is inserted or removed, which bumps the epoch, and the
// collector doesn't move tables. Field reads and writes go through the
// address; the paths repairing a witness after the epoch changes find the
// entry again by its index.

pub struct RunState<'src, 'intern> {
    pub base: usize,
    // Dynamic stack top (à la Lua's `L->top`): delimits variable-count spans
    // (MULTRET call args/results, SETLIST, vararg). Distinct from `vals`'s
    // length, which is the register-file allocation and is never shrunk below a
    // live frame. Fixed-register ops index `base + reg`; only the variable-count
    // (`b == 0` / `c == 0`) handlers read up to `top`.
    pub top: usize,
    // The largest register-file extent (`base + max_stack`) over all live frames.
    // `vals` must never be truncated below this, or a suspended outer frame would
    // lose registers it still reads. Maintained by `call_lua`/`do_return` (saved as
    // each frame's `limit`). See Note [Stack frames].
    pub natural_max: usize,
    pub vals: ValueStack<'src, 'intern>,
    pub pc: usize,
    pub _G: Tc<Table<'src, 'intern>>,
    pub clos: Tc<LClosure<'src, 'intern>>,
    pub upvals: FVec<(Upvalue<'src, 'intern>, FVec<Tc<Upvalue<'src, 'intern>>>)>,
    pub callstack: FVec<CallstackEntry<'src, 'intern>>,
    pub counters: PerfCounters,
    pub select: usize,
    pub witness_base: usize,
    /// The end of the innermost frame's hash witnesses. See Note [Hash witnesses].
    pub witness_top: usize,
    pub hash_witnesses: FVec<HashWitness>,
    pub trap: bool,
    pub current_off: u16,
    pub gas: i64,
    /// Prototypes whose entry blocks `closure.__jit = ...` asked to compile, for
    /// `Specializer::run` to force (feature `magic`). See `emit_settable`.
    #[cfg(feature = "magic")]
    pub force_jit: FVec<LProto<'src, 'intern>>,
    /// Intern arena for canonicalizing owned strings at box time.
    pub intern: &'intern internment::Arena<IStr<'src>>,
}

// Manual `Debug` (the `intern` arena isn't `Debug`); skips it and the counters.
impl<'src, 'intern> Debug for RunState<'src, 'intern> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RunState")
            .field("base", &self.base)
            .field("pc", &self.pc)
            .field("vals", &self.vals)
            .field("select", &self.select)
            .field("trap", &self.trap)
            .field("gas", &self.gas)
            .finish_non_exhaustive()
    }
}

impl<'src, 'intern> RunState<'src, 'intern> {
    /// Close the running frame's open upvalues, the slots from `base` up: each takes the
    /// slot's value into a cell of its own, as it leaves the stack. An enclosing frame's
    /// stay open. See Note [Captured slots] in `generator`.
    pub fn close_upvalues(&mut self, owner: &mut Owner)
    {
        let (base, vals) = (self.base, &self.vals);
        self.upvals.retain(|(upval, uses)| {
            let Upvalue::Open(idx) = upval else { unreachable!("a closed upvalue in the open list") };
            if *idx < base {
                return true;
            }
            let closed = Tc::new(vals[*idx]);
            for up_use in uses.iter() {
                up_use.replace(owner, Upvalue::Closed(closed.clone()));
            }
            false
        });
    }

    #[inline(always)]
    // Natives take `LBoxed` slice views over the arg/return stack regions, so the
    // boxed stack is aliased in place with no unbox/rebox copy.
    pub fn call_native(&mut self, nf: NativeFunc, a: u16, b: u16, c: u16, owner: &mut Owner) {
        // The function's slot and its arguments: up to the top when they are
        // all a previous call's results (`B` = 0), else `B - 1` of them.
        let end = if b == 0 { self.top } else { self.base + a as usize + b as usize };
        let args = &self.vals[self.base + a as usize + 1..end];
        debug!("{:?}", args);
        let returns = if c == 0 {
            // Every result, in the slots the function and its arguments took.
            &self.vals[self.base + a as usize..end]
        }
        else if c == 1 {
            // nothing saved
            &[]
        } else if c >= 2 {
            &self.vals[self.base + a as usize..=self.base + a as usize + c as usize - 2]
        } else {
            unimplemented!()
        };
        let wanted = returns.len();
        let mut count = 0;
        LCellOwner::scope(|mut seq| {
            // Safety: LCellOwner guarantees that the native function can only ever
            // have mutable access to one slice at a time. The transmute wraps the
            // aliased stack slices in-place as `LCell`s (repr(transparent) over UnsafeCell).
            let args = unsafe { core::mem::transmute(seq.cell(args)) };
            let returns = unsafe { core::mem::transmute(seq.cell(returns)) };
            count = (nf)(seq, args, returns, owner);
        });
        // Taking every result, the caller reads up to the top.
        if c == 0 {
            self.top = self.base + a as usize + count.min(wanted);
        }
    }

    // `extern "C"` so the JIT can call it directly. The callee closure is read
    // from slot `a` of the boxed stack, and the return location arrives packed
    // into a single word (see `ReturnLocation::pack`).
    pub extern "C" fn call_lua(&mut self, owner: &mut Owner,
        ret: PackedLocation, a: u16, b: u16, c: u16) -> usize
    {
        let LValue::LClosure(lclos) = self.vals[self.base + a as usize].unbox() else { unreachable!() };
        let ret_loc = ReturnLocation::unpack(ret);
        // record call stack: we say where to return to and where to put the values
        let next_stack = unsafe { (*lclos.ro(owner).prototype).max_stack as usize };
        let next_base = self.base + a as usize + 1;
        // The max-extent over the caller and its own ancestors, restored on return so
        // the stack (and the GC's mark range) shrinks back as frames pop. See Note
        // [Stack frames].
        let limit = self.natural_max;
        // push empty stack frame
        if next_base + next_stack > self.vals.len() {
            self.vals.resize_with(next_base + next_stack, || LBoxed::NIL);
        }
        // The parameters the call doesn't pass are nil: their slots may hold what an
        // earlier frame left there. Its arguments are `b - 1` values, or up to the top.
        let passed = if b == 0 { self.top } else { next_base + b as usize - 1 };
        let params = next_base + unsafe { (*lclos.ro(owner).prototype).param_count as usize };
        for slot in passed..params {
            self.vals[slot] = LBoxed::NIL;
        }
        // The callee's frame extends the live max-extent while it runs.
        self.natural_max = self.natural_max.max(next_base + next_stack);
        self.callstack.push(CallstackEntry {
            clos: self.clos.clone(),
            ret: ret_loc,
            frame: self.base,
            limit,
            rloc: self.base + a as usize,
            witness_frame: self.witness_base,
            witness_top: self.witness_top,
            c
        });
        self.base = next_base;
        // Start `top` at the end of the callee's register file.
        self.top = next_base + next_stack;
        self.witness_base = self.witness_top;
        self.clos = lclos.clone();
        next_stack
    }

    /// Return from the running frame to its caller's `ReturnLocation`, the results
    /// moved in place to the call's, or, from the outermost frame, the range of
    /// the stack its results are in, which the caller takes off it.
    pub fn do_return(&mut self, owner: &mut Owner, a: usize, b: usize) -> Result<ReturnLocation, std::ops::Range<usize>> {
        // we're going to be removing this frame, so close any open
        // upvalues.
        self.close_upvalues(owner);

        // The results: `b - 1` values from R(A), or every value up to the top.
        let from = self.base + a;
        let count = if b == 0 { self.top - from } else { b - 1 };
        match self.callstack.pop() {
            Some(CallstackEntry { clos: ret_clos, ret, frame, limit, witness_frame, witness_top, rloc, c }) => {
                debug!("{} {:?} {}", self.base, unsafe { &(*ret_clos.ro(owner).prototype).instructions }, c);
                self.clos = ret_clos.clone();
                self.base = frame;
                self.witness_base = witness_frame;
                // The callee frame is gone; the live max-extent is the caller's again.
                self.natural_max = limit;
                // The results move down to the caller's `rloc`, in place: exactly `c
                // - 1`, padded with nil, or with C = 0 (MULTRET) all of them.
                let wanted = if c == 0 { count } else { c as usize - 1 };
                let moved = wanted.min(count);
                self.vals.copy_within(from..from + moved, rloc);
                for slot in rloc + moved..rloc + wanted {
                    self.vals[slot] = LBoxed::NIL;
                }
                self.top = rloc + wanted;
                // Shrink the register file back to the caller's extent (`limit`) so the
                // popped callee frame stops being marked by the GC, but for MULTRET
                // results past it. See Note [Stack frames].
                self.vals.truncate(if c == 0 { limit.max(rloc + wanted) } else { limit });
                self.witness_top = witness_top;
                return Ok(ret)
            },
            None => Err(from..from + count),
        }
    }
}

impl<'src, 'intern> RunState<'src, 'intern> {
    /// The table in `slot` of the running frame.
    pub fn table_at(&self, slot: usize) -> Tc<Table<'src, 'intern>> {
        let LValue::Table(tab) = self.vals[self.base + slot].unbox() else { unreachable!("slot {slot} holds no table") };
        tab
    }
}

impl<'src, 'intern> Mark for RunState<'src, 'intern> {
    fn mark(&self, owner: &Owner) {
        for val in self.vals.iter() {
            val.mark(owner);
        }
        self.clos.mark(owner);
        self._G.mark(owner);
        // The open upvalues' cells, which `close_upvalues` closes when their frame
        // returns: a closure capturing one may be garbage before then. Their values
        // are the stack's, marked above.
        for (_, cells) in self.upvals.iter() {
            for cell in cells.iter() {
                cell.mark(owner);
            }
        }
        // Our callstack isn't actually guaranteed to be accurate, because it could be lagging due
        // to being inside the JIT with a native call frame instead. However, we would only end up
        // missing closures which were already rooted by the JIT, so it's fine.
        for call in self.callstack.iter() {
            call.clos.mark(owner);
        }
    }
}

impl<'src, 'intern> Vm<'src, 'intern> {
    pub fn new(top_level: LProto<'src, 'intern>) -> Self {
        Heap::init();
        Self { top_level }
    }

    pub(crate) fn global_env(&self, intern: &'intern internment::Arena<IStr<'src>>) -> Tc<Table<'src, 'intern>> {
        let mut math_tab = Table::new(0, 0);
        // Unary float builtins consume the boxed stack directly: decode the one
        // argument with `as_number()` and write the result back as a boxed double.
        macro_rules! math1 {
            ($f:expr) => {
                LValue::NClosure(NClosure::new(|mut seq, args, returns, _owner| {
                    let r = match args.ro(&seq) {
                        [b] => LBoxed::from_number(($f)(b.as_number().unwrap_or_else(|| unimplemented!()))),
                        _ => unimplemented!(),
                    };
                    returns.rw(&mut seq).into_iter().zip([r]).for_each(|(slot, o)| *slot = o);
                    1
                }))
            };
        }
        math_tab.insert_lvalue(InternString::intern(intern, "floor"), math1!(f64::floor));
        math_tab.insert_lvalue(InternString::intern(intern, "ceil"), math1!(f64::ceil));
        math_tab.insert_lvalue(InternString::intern(intern, "sqrt"), math1!(f64::sqrt));
        math_tab.insert_lvalue(InternString::intern(intern, "abs"), math1!(f64::abs));
        math_tab.insert_lvalue(InternString::intern(intern, "huge"), LValue::NClosure(NClosure::new(|mut seq, args, returns, _owner|{
            returns.rw(&mut seq).into_iter().next().map(|r| *r = LBoxed::from_number(f64::INFINITY));
            1
        })));
        math_tab.insert_lvalue(InternString::intern(intern, "pi"), LValue::Number(Number(std::f64::consts::PI)));
        math_tab.insert_lvalue(InternString::intern(intern, "sin"), math1!(f64::sin));
        math_tab.insert_lvalue(InternString::intern(intern, "cos"), math1!(f64::cos));
        math_tab.insert_lvalue(InternString::intern(intern, "tan"), math1!(f64::tan));

        let mut os_tab = Table::new(0, 0);
        os_tab.insert_lvalue(InternString::intern(intern, "exit"), LValue::NClosure(NClosure::new(|seq, args, _returns, _owner| {
            match args.ro(&seq) {
                [b] => std::process::exit(b.as_number().unwrap_or_else(|| unimplemented!()) as i32),
                _ => unimplemented!(),
            }
        })));

        let math = (InternString::intern(intern, "math"), LValue::Table(Tc::new(math_tab)));
        let os = (InternString::intern(intern, "os"), LValue::Table(Tc::new(os_tab)));
        let _g = Tc::new(Table {
            array: vec![].into(),
            hash: IndexMap::<_, _, InternedHasher>::from_iter(
                vec![
                (InternString::intern(intern, "print"), LValue::NClosure(NClosure::new(|seq, args, _returns, owner| {
                    let s = args.ro(&seq).iter().map(|val| val.unbox().as_string(owner)).flat_map(|maybe_str|
                        maybe_str.map(|s| -> String { String::from(String::from_utf8_lossy(s.as_slice()).to_owned()) })
                    ).collect::<Vec<_>>();
                    //println!("> {}", String::from_utf8_lossy(s.iter().into()));
                    println!("{}", s.iter().intersperse(&"\t".to_string()).cloned().collect::<String>());
                    0
                }))),
                (InternString::intern(intern, "assert"), LValue::NClosure(NClosure::new(|seq, args, _returns, _owner| {
                    if let [b, ..] = args.ro(&seq) {
                        if let LValue::Bool(false) = b.unbox() {
                            panic!("lua assert failed");
                        }
                    }
                    0
                }))),
                // Lua's `collectgarbage(opt [, arg])`: drive the collector explicitly.
                (InternString::intern(intern, "collectgarbage"), LValue::NClosure(NClosure::new(|mut seq, args, returns, owner| {
                    let opt: Vec<u8> = match args.ro(&seq).get(0).map(|b| b.unbox()) {
                        Some(LValue::InternedString(s)) => s.as_bytes().to_vec(),
                        Some(LValue::OwnedString(s)) => s.as_slice().to_vec(),
                        _ => b"collect".to_vec(),
                    };
                    let result: LValue = match opt.as_slice() {
                        // SAFETY: reachable only from a safepoint that just published roots.
                        // See Note [GC roots].
                        b"collect" | b"" => { unsafe { GcCtx::assume_rooted().full_collect_published(owner); } LValue::Number(Number(0.0)) },
                        // Live memory in Kbytes, as a (fractional) number.
                        b"count" => LValue::Number(Number(Heap::live_bytes() as f64 / 1024.0)),
                        // Advance one incremental step.
                        b"step" => { unsafe { GcCtx::assume_rooted().step_published(owner); } LValue::Bool(false) },
                        b"stop" => { Heap::set_gc_off(true); LValue::Number(Number(0.0)) },
                        b"restart" => { Heap::set_gc_off(false); LValue::Number(Number(0.0)) },
                        // Tuning knobs we accept but don't model.
                        b"setpause" | b"setstepmul" => LValue::Number(Number(0.0)),
                        _ => LValue::Nil,
                    };
                    returns.rw(&mut seq).into_iter().next().map(|r| *r = LBoxed::box_lvalue(result));
                    1
                }))),
                math,
                os,
                ].into_iter().chain(crate::library::globals(intern)).map(|(k, v)| (LCanon(LBoxed::box_lvalue(k)), LBoxed::box_lvalue(v)))
            ),
            epoch: 0,
            environment: true,
        });
        // `_g` needs no explicit root: it lives in the `RunState` (`RunState::mark` shades it)
        // for the whole run, which is the only time a collection can see it. See Note [GC roots].
        _g
    }

    pub fn rk<'exec>(proto: LProto<'src, 'intern>, base: usize, vals: &'exec ValueStack<'src, 'intern>, r: u16)
        -> Result<&'exec LConstant<'src, 'intern>, &'exec LBoxed<'src, 'intern>>
    {
        if (r & 0x100)!=0 {
            let r_const = r & (0xff);
            debug!("rk {}", r_const);
            Ok(unsafe { &(&(*proto).constants.items)[r_const as usize] })
        } else {
            Err(&vals[base + r as usize])
        }
    }

    /// Run `body` in a generative GC scope. `body` gets a [`Scoped`] view of the VM and arena
    /// branded with a fresh `'gc`; GC values it produces stay confined to the closure, and the
    /// heap is freed when it returns, so only GC-free data may be returned out. Panics if a
    /// scope is already active on this thread. See Note [Scoped heap].
    pub fn scope<R>(
        &self,
        intern: &'intern internment::Arena<IStr<'src>>,
        owner: &mut Owner,
        body: impl for<'gc> FnOnce(Scoped<'gc>, &mut Owner) -> R,
    ) -> R {
        let _guard = ScopeGuard::enter();
        let root_scope = Heap::root_scope();
        // SAFETY: `Scoped::vm`/`intern` read the erased pointers back at `'gc`, which must not
        // outlive `'src`/`'intern`. `'gc` is not caller-chosen: the only `'gc`-carrying field is
        // `gc`, and `RootScope::token` returns `GcCtx<'lua>` borrowing the local `root_scope`.
        // `GcCtx` (hence `Scoped`) is invariant, so `body(scoped, ..)` instantiates `for<'gc>`
        // at exactly `'gc = 'lua`. A borrow of a local can't outlive this call, and `'src`/
        // `'intern` outlive it (they back `&self`/`intern`), so `'src: 'gc` and `'intern: 'gc`:
        // the reads only shorten lifetimes. `for<'gc>` then confines every `'gc` value to
        // `body`, so `Heap::reset` frees an unreachable heap.
        let scoped = Scoped {
            vm: self as *const Vm<'src, 'intern> as *const (),
            intern: intern as *const internment::Arena<IStr<'src>> as *const (),
            gc: root_scope.token(),
        };
        let r = body(scoped, owner);
        Heap::reset();
        r
    }

    /// Resolve an RK operand straight to a boxed value (a constant becomes
    /// boxed, a register is copied).
    #[inline(always)]
    pub fn rk_boxed(rk: Result<&LConstant<'src, 'intern>, &LBoxed<'src, 'intern>>) -> LBoxed<'src, 'intern> {
        match rk {
            Ok(c) => LBoxed::from(c),
            Err(lb) => *lb,
        }
    }

    /// Run a closure in the specializer, gated behind the scope's `GcCtx` token. Crate-private
    /// so the only way in is [`Scoped::run`]. See Note [Scoped heap].
    pub(crate) fn run<'lua, 'gc>(&'lua self,
        gc: GcCtx<'gc>,
        owner: &mut Owner,
        mut _G: Tc<Table<'src, 'intern>>,
        mut clos: Tc<LClosure<'src, 'intern>>,
        mut args: ValueStack<'src, 'intern>,
        intern: &'intern internment::Arena<IStr<'src>>,
    )
        -> Result<FVec<LValue<'src, 'intern>>, Box<dyn Error>>
        where 'src: 'lua
    {
        args.resize_with(unsafe {
            (*clos.ro(owner).prototype).max_stack as usize
        }, || LBoxed::NIL);
        // The global `_G` is the global environment, as Lua's base library sets it.
        let env = LBoxed::box_lvalue(LValue::Table(_G.clone()));
        _G.set(owner, LBoxed::box_lvalue(InternString::intern(intern, "_G")), env, intern);

        let mut spec = Specializer::new(clos.clone());
        let mut state = {
            let mut vals = args;
            // The top-level frame occupies the whole allocated register file.
            let top = vals.len();
            let mut upvals: FVec<(Upvalue<'src, 'intern>, FVec<Tc<Upvalue<'src, 'intern>>>)> = vec![].into();
            let mut base = 0;
            let mut witness_base = 0;
            let mut pc = 0;
            let mut callstack: FVec<_> = vec![].into();

            RunState {
                base,
                top,
                natural_max: top,
                witness_base,
                witness_top: 0,
                pc,
                _G,
                clos,
                vals,
                upvals,
                callstack,
                counters: Default::default(),
                hash_witnesses: vec![].into(),
                select: 0,
                trap: false,
                #[cfg(feature = "magic")]
                force_jit: vec![].into(),
                current_off: 0,
                gas: std::env::var("LUNACY_GAS").ok().and_then(|v| v.parse().ok()).unwrap_or(i64::MAX),
                intern,
            }
        };
        // `gc` is the scope's rooting token, threaded in by `Scoped::run`; the rooting scope
        // stays live for the whole `Vm::scope`. See Note [GC roots].
        //
        // The entry closure runs in the specializer from its first instruction, as a call
        // does: its frame is the whole register file, and with no caller to return to, its
        // return ends the run.
        let entry = state.clos.clone();
        let ctx = Rc::new(Context::new(vec![LType::Unknown; state.vals.len()]));
        spec.versions.entry(entry.ro(owner).prototype).or_insert_with(|| HashMap::default());
        spec.set_current(entry);
        let block = spec.version(owner, 0, ctx);
        let (state, r_vals) = spec.run(gc, owner, block, state);
        #[cfg(all(feature = "counters", not(test)))] {
            println!("counters after run {:?} instructions {:?}", state.counters, spec.count());
        }

        #[cfg(feature = "graph")]
        for proto in unsafe { &(*self.top_level).prototypes.items } {
            let outfile = format!("func_{}.pdf", proto.line_defined);
            spec.dump(owner, proto, outfile.as_str());
        }

        // Decode the boxed return values back into the `LValue` view for callers.
        Ok(r_vals.into_iter().map(|b| b.unbox()).collect::<Vec<_>>().into())
    }

}
