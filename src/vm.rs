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

use crate::specialize::{Specializer, Context, SubPc};

// `BlockId` and `HashRef` are referenced by `Location` / `HashWitness`, so they
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
    /// The array part's kind: the representations of the values stored in it
    /// since it was last emptied, a bit each (`LType::bit`). It is of a single
    /// kind when one bit is set. See Note [Array kinds] in `specialize`.
    pub kind: u8,
}

/// How a store into an array part widens its kind. See Note [Array kinds] in
/// `specialize`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, core::marker::ConstParamTy)]
pub enum Widen {
    /// The kind has the value's representation already.
    No,
    /// By the value's representation, known when compiling.
    Bit(LType),
    /// By the value's representation, found out from its tag.
    Decode,
}

thread_local! {
    /// How many times the global environment's hash entries have moved: global
    /// caches holding an entry's address are valid while it's unchanged. See
    /// Note [Global caches] in `specialize`.
    static ENV_MOVES: Cell<u64> = const { Cell::new(0) };
}

/// See `ENV_MOVES`.
pub fn env_moves() -> u64 {
    ENV_MOVES.with(|moves| moves.get())
}

impl<'src, 'intern> Table<'src, 'intern> {
    pub fn new(array: usize, hash: usize) -> Self {
        Self {
            array: Vec::with_capacity(array).into(),
            hash: IndexMap::with_capacity_and_hasher(hash, InternedHasher::default()),
            epoch: 0,
            environment: false,
            kind: 0,
        }
    }

    /// Note a value of representation `t` stored in the array part. See Note
    /// [Array kinds] in `specialize`.
    #[inline(always)]
    pub fn widen_kind(&mut self, t: LType) {
        self.kind |= t.bit();
    }

    /// Note `value` stored in the array part, as `how` says.
    #[inline(always)]
    pub fn widen_by(&mut self, how: Widen, value: LBoxed<'src, 'intern>) {
        match how {
            Widen::No => {}
            Widen::Bit(t) => self.widen_kind(t),
            Widen::Decode => self.widen_kind(value.representation()),
        }
    }

    /// Drop the nils ending the array part. See Note [Array length].
    pub fn trim(&mut self) {
        while self.array.last().is_some_and(|value| value.bits() == LBoxed::NIL.bits()) {
            self.array.pop();
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

// Note [Array length]
// ~~~~~~~~~~~~~~~~~~~
// A table's length (`#t`) is a border: an index whose value isn't nil and
// whose successor's is, or zero if `t[1]` is nil. The array part holds the keys
// from 1 up to its length, and never ends in nil, so its length is a border.
// Every store into it keeps that: nil stored into its last element drops the
// nils ending it, and nil stored past its end stores nothing. A window op
// storing a value the context knows isn't nil has nothing to check.

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
        if self.barrier_pending() {
            self.barrier_slow();
        }
    }

    /// Whether a store into this table needs its backward barrier
    /// (`barrier_slow`): only in a collection cycle. See Note [Write barriers].
    #[inline]
    pub fn barrier_pending(&self) -> bool {
        // Nothing is black outside a collection cycle. See Note [Write barriers].
        debug_assert!(crate::gc::gc_in_progress() || !self.0.is_black(), "a black table outside a collection cycle");
        crate::gc::gc_in_progress()
    }

    /// The backward barrier, in a collection cycle. See Note [Write barriers].
    #[inline]
    pub fn barrier_slow(&self) {
        self.0.backward_barrier();
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
        self.set_widening::<{ Widen::Decode }>(owner, key, value, intern)
    }

    /// `set`, a value stored in the array part widening its kind as `W` says.
    #[inline]
    pub fn set_widening<const W: Widen>(&mut self, owner: &mut Owner, key: LBoxed<'src, 'intern>, value: LBoxed<'src, 'intern>, intern: &'intern internment::Arena<IStr<'src>>) {
        if let Some(n) = key.as_number() {
            return self.set_number_widening::<W>(owner, n, value);
        }
        self.barrier_back();
        let k = LCanon::new(key, intern);
        self.rw(owner).insert_hash(k, value);
        self.rw(owner).epoch += 1;
    }

    /// Look up a number key, which needs no intern arena to canonicalize.
    pub fn get_number(&self, owner: &Owner, n: f64) -> LBoxed<'src, 'intern> {
        match array_slot(n) {
            Some(slot) => self.ro(owner).array.get(slot).copied().unwrap_or(LBoxed::NIL),
            None => self.ro(owner).hash.get(&LCanon::number(n)).copied().unwrap_or(LBoxed::NIL),
        }
    }

    /// `set` of a number key, which needs no intern arena to canonicalize.
    pub fn set_number(&mut self, owner: &mut Owner, n: f64, value: LBoxed<'src, 'intern>) {
        self.set_number_widening::<{ Widen::Decode }>(owner, n, value)
    }

    /// `set_widening` of a number key.
    #[inline]
    fn set_number_widening<const W: Widen>(&mut self, owner: &mut Owner, n: f64, value: LBoxed<'src, 'intern>) {
        self.barrier_back();
        if let Some(slot) = array_slot(n) {
            // Nil past the end is no store, and nil into the last element
            // shortens the array part. See Note [Array length].
            if value.bits() == LBoxed::NIL.bits() {
                if slot < self.ro(owner).array.len() {
                    self.rw(owner).array[slot] = value;
                    self.rw(owner).widen_by(W, value);
                    self.rw(owner).trim();
                }
                return;
            }
            // TODO: sparse arrays
            if self.rw(owner).array.len() <= slot {
                if self.rw(owner).array.len() < slot {
                    // The hole past the end, filled with nil.
                    self.rw(owner).widen_kind(LType::Nil);
                }
                self.rw(owner).array.resize_with(slot + 1, || LBoxed::NIL);
            }
            self.rw(owner).array[slot] = value;
            self.rw(owner).widen_by(W, value);
            return;
        }
        self.rw(owner).insert_hash(LCanon::number(n), value);
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
#[derive(Debug, Clone)]
pub enum LValue<'src, 'intern> {
    Nil = 0,
    Bool(bool) = 1,
    // Numbers, in the encoding their box has: the integer one, or the double
    // one (Note [Integer encoding] in `lboxed`). Lua can't tell 2 from 2.0:
    // equality and comparisons are by value.
    Integer(i32) = 2,
    Double(Number) = 16,
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
            LValue::Integer(i) => Self::number(i as f64),
            LValue::Double(n) => Self::number(n.0),
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

    /// The key whose `boxed().bits()` are `bits`.
    ///
    /// # Safety
    /// `bits` must be an `LCanon`'s, and a value it names still live.
    #[inline(always)]
    pub unsafe fn from_bits(bits: u64) -> Self {
        LCanon(LBoxed::from_bits(bits))
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, core::marker::ConstParamTy)]
pub enum LType {
    Unknown,
    Nil,
    Bool,
    String,
    Closure,
    Table,
    /// A number in the integer encoding. See Note [Integer encoding] in `lboxed`.
    Integer,
    /// A number in the double encoding.
    Double,
}

impl LType {
    /// This representation's bit in an array part's kind. See Note [Array
    /// kinds] in `specialize`.
    #[inline(always)]
    pub const fn bit(self) -> u8 {
        1 << self as u8
    }

    /// Whether a value of type `other` is one of type `self`: `other` is
    /// `self`, or `self` is `Unknown`.
    pub fn accepts(self, other: LType) -> bool {
        self == other || self == LType::Unknown
    }

    /// The most specific type accepting both.
    pub fn join(self, other: LType) -> LType {
        if self == other { self } else { LType::Unknown }
    }
}

impl std::fmt::Display for LType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LType::Unknown => write!(f, "?"),
            LType::Nil => write!(f, "nil"),
            LType::Bool => write!(f, "bool"),
            LType::String => write!(f, "string"),
            LType::Closure => write!(f, "func"),
            LType::Table => write!(f, "table"),
            LType::Integer => write!(f, "integer"),
            LType::Double => write!(f, "double"),
        }
    }
}

impl<'src, 'intern> PartialEq for LValue<'src, 'intern> {
    /// Lua's raw equality: numbers by value, whichever their encodings.
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (LValue::Nil, LValue::Nil) => true,
            (LValue::Bool(a), LValue::Bool(b)) => a == b,
            (LValue::Table(a), LValue::Table(b)) => a == b,
            (LValue::InternedString(a), LValue::InternedString(b)) => a == b,
            (LValue::OwnedString(a), LValue::OwnedString(b)) => a.as_slice() == b.as_slice(),
            (LValue::InternedString(a), LValue::OwnedString(b)) | (LValue::OwnedString(b), LValue::InternedString(a)) =>
                a.as_bytes() == b.as_slice(),
            (LValue::LClosure(a), LValue::LClosure(b)) => a == b,
            (LValue::NClosure(a), LValue::NClosure(b)) => a == b,
            (a, b) => match (a.as_f64(), b.as_f64()) {
                (Some(a), Some(b)) => a == b,
                _ => false,
            },
        }
    }
}

impl<'src, 'intern> LValue<'src, 'intern> {
    /// A number, in the encoding `LBoxed::from_number` gives it: the integer
    /// one for a whole i32 (not -0), else the double one.
    pub fn number(n: f64) -> Self {
        if crate::lboxed::is_integer(n) { LValue::Integer(n as i32) } else { LValue::Double(Number(n)) }
    }

    /// A number's value, whichever its encoding.
    pub fn as_f64(&self) -> Option<f64> {
        match self {
            LValue::Integer(i) => Some(*i as f64),
            LValue::Double(n) => Some(n.0),
            _ => None,
        }
    }

    pub fn compare(&self, opcode: Opcode, right: Self, owner: &Owner) -> Result<bool, String> {
        // TODO: metamethods
        let numbers = self.as_f64().is_some() && right.as_f64().is_some();
        if !numbers && std::mem::discriminant(self) != std::mem::discriminant(&right) {
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
                    (left, right) if numbers => Ok(left.as_f64() < right.as_f64()),
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
                    (left, right) if numbers => Ok(left.as_f64() <= right.as_f64()),
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
        match (self.as_f64(), right.as_f64()) {
            (Some(left_n), Some(right_n)) => {
                match opcode {
                    Opcode::ADD => Ok(LValue::number(left_n + right_n)),
                    Opcode::SUB => Ok(LValue::number(left_n - right_n)),
                    Opcode::MUL => Ok(LValue::number(left_n * right_n)),
                    Opcode::DIV => Ok(LValue::number(left_n / right_n)),
                    Opcode::MOD => Ok(LValue::number(lua_mod(left_n, right_n))),
                    Opcode::POW => Ok(LValue::number(left_n.powf(right_n))),
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
            LValue::InternedString(s) => Ok(LValue::number(s.as_bytes().len() as _)),
            LValue::OwnedString(s) => Ok(LValue::number(s.len() as _)),
            // A border. See Note [Array length].
            LValue::Table(t) => Ok(LValue::number(t.ro(owner).array.len() as _)),
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
            LValue::Integer(i) => { write!(s, "{}", i); },
            LValue::Double(f) => { write!(s, "{}", f.0); },
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
            LValue::Integer(i) => { write!(s, "{}", i); },
            LValue::Double(f) => { write!(s, "{}", f.0); },
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
            Constant::Number(n) => LValue::number(n.0),
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
    pub args: crate::specialize::CType,
    pub result: crate::specialize::CType,
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

/// A place in the specializer's code: a block, and the offset of a residual in
/// it. Where a call returns to, where JIT code exits to the interpreter, and so
/// on.
#[derive(Debug)]
pub struct Location(pub BlockId, pub usize);

/// A [`Location`] in one register-sized word, `(off << 32) | block` (see
/// [`Location::pack`]). `#[repr(transparent)]` over `usize`, so it crosses the
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

    /// The location `bits` are, as `bits` gives them.
    #[inline(always)]
    pub fn from_bits(bits: usize) -> Self {
        PackedLocation(bits)
    }
}

impl Location {
    /// This location in one word. See `PackedLocation`.
    pub fn pack(self) -> PackedLocation {
        let Location(BlockId(block), off) = self;
        PackedLocation((off << 32) | block)
    }

    pub fn unpack(p: PackedLocation) -> Self {
        Location(BlockId(p.0 & 0xffff_ffff), p.0 >> 32)
    }
}

/// What a return leaves JIT code with, or last sets `RunState::returned` to:
/// `RETURNED | effects << EFFECTS_SHIFT | id`, `id` naming what it returned
/// and `effects` its function's. See Notes [Call continuations] and [Call
/// effects] in `specialize`.
pub const RETURNED: u64 = (-5i32 as u64) << 32;
/// Where a return's effects are in what it returns, above its id. See
/// `RETURNED`.
pub const EFFECTS_SHIFT: u32 = 20;

// Note [Stack frames]
// ~~~~~~~~~~~~~~~~~~~~
// A call frame occupies `max_stack` slots of the register file (`vals`) from its
// `base`; `RunState::top` is its dynamic Lua top (the variable-count-span cursor).
// `call_lua` records the caller's state and the callee's function slot in a
// `CallstackEntry` and makes the stack long enough for the callee's frame; a return pops it and restores that state
// (`leave`), and the caller takes the results (`arrive`). See Note [Returns].
//
// The stack's length is the most any frame has reached since the GC last marked
// it, not what is live. The GC marks the stack up to its live extent
// (`RunState::live_extent`): the most of each live frame's `base + max_stack`,
// the running one's and each caller's in the callstack, and of the top, which is
// past them while results a call returned all of (C = 0) are still to be
// consumed. It is computed when the GC runs, from the callstack, rather than
// kept on each call and return.
//
// Marking the stack shrinks it to its live extent (`RunState::mark`), and the
// GC marks the roots again, the mutator stopped, before it sweeps: so a slot
// whose value the GC doesn't mark, which it may free, is past the stack's end
// by then. The stack grows back only by a callee's frame, which a call nils past
// the arguments the caller wrote (`push_frame`). So every slot of the stack
// names something live.

// Note [Vararg frames]
// ~~~~~~~~~~~~~~~~~~~~
// A vararg function's frame starts past all of its arguments: the extra ones,
// past its fixed parameters, stay where its caller wrote them, just below the
// frame, which starts with a copy of the fixed ones. VARARG reads them from
// there, and a return puts its results in the function's slot below them.
//
// A vararg frame's callstack entry records its function's slot, as Lua's call
// info does: its extra arguments are the slots past its function's and its fixed
// arguments' up to its base, and its return puts results in that slot. Any other
// frame's function's slot is just below its base, so its entry needn't record
// it. Whether a frame's function is vararg is static at its calls (once the
// callee is known) and at its returns. The outermost frame, a chunk, has no extra
// arguments.

/// A frame's caller's state, restored when it returns, and, for a vararg
/// function's frame, its function's slot. See Note [Stack frames].
#[derive(Debug)]
pub struct CallstackEntry<'src, 'intern> {
    pub clos: Tc<LClosure<'src, 'intern>>,
    pub ret: Location,
    pub frame: usize,
    /// The slot of the frame's function, where its results go: initialized in
    /// exactly the entries of vararg functions' frames. `call_lua` pushes every
    /// vararg function's frame, and sets it; `PushFrame` pushes only frames of
    /// functions that aren't vararg, and leaves it uninitialized. See Note
    /// [Vararg frames].
    func: core::mem::MaybeUninit<usize>,
    pub witness_frame: usize,
    pub witness_top: usize,
}

impl<'src, 'intern> CallstackEntry<'src, 'intern> {
    /// The slot of the function of this entry's frame.
    ///
    /// # Safety
    ///
    /// The frame's function is vararg: `func` is initialized in exactly those
    /// frames' entries.
    unsafe fn vararg_func(&self) -> usize {
        // SAFETY: the caller's.
        unsafe { self.func.assume_init() }
    }
}

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
//
// JIT code reads a witness inline (`GuardWitness`), so `Witnesses` keeps the
// address of the first one where it can load it: only growing the vector moves
// it, and only `Witnesses::grow` grows it.

/// The hash witnesses of every frame. See Note [Hash witnesses].
pub struct Witnesses {
    /// The address of the first witness, for JIT code (`Witnesses::DATA`).
    data: *mut HashWitness,
    vec: FVec<HashWitness>,
}

impl Witnesses {
    /// Where in a `Witnesses` the first witness's address is.
    pub const DATA: usize = core::mem::offset_of!(Witnesses, data);

    pub fn new() -> Self {
        let mut vec: FVec<HashWitness> = vec![].into();
        Witnesses { data: vec.as_mut_ptr(), vec }
    }

    pub fn len(&self) -> usize {
        self.vec.len()
    }

    /// Make room for `len` witnesses.
    pub fn grow(&mut self, len: usize) {
        if self.vec.len() < len {
            self.vec.resize_with(len, HashWitness::default);
            self.data = self.vec.as_mut_ptr();
        }
    }
}

impl Index<usize> for Witnesses {
    type Output = HashWitness;
    fn index(&self, index: usize) -> &HashWitness {
        &self.vec[index]
    }
}

impl IndexMut<usize> for Witnesses {
    fn index_mut(&mut self, index: usize) -> &mut HashWitness {
        &mut self.vec[index]
    }
}

pub struct RunState<'src, 'intern> {
    pub base: usize,
    // Dynamic stack top (à la Lua's `L->top`): delimits variable-count spans
    // (MULTRET call args/results, SETLIST, vararg). Distinct from `vals`'s
    // length, the most any frame has reached since the GC last marked it (Note
    // [Stack frames]).
    // Fixed-register ops index `base + reg`; only the variable-count
    // (`b == 0` / `c == 0`) handlers read up to `top`.
    pub top: usize,
    pub vals: ValueStack<'src, 'intern>,
    pub pc: usize,
    pub _G: Tc<Table<'src, 'intern>>,
    pub clos: Tc<LClosure<'src, 'intern>>,
    pub upvals: FVec<(Upvalue<'src, 'intern>, FVec<Tc<Upvalue<'src, 'intern>>>)>,
    pub callstack: FVec<CallstackEntry<'src, 'intern>>,
    pub counters: PerfCounters,
    pub select: usize,
    /// The record of the site whose window op's cold stencil is running. See
    /// Note [Cold stencils] in `window`.
    pub cold_site: *const u64,
    /// The last return's `RETURNED | effects << EFFECTS_SHIFT | id`, `id`
    /// naming what it returned and `effects` its function's, which
    /// the continuation of the call it returned from guards on. See Note [Call
    /// continuations] in `specialize`.
    pub returned: u64,
    /// Where the caller of the last return from JIT code continues, a
    /// `PackedLocation`, for the run loop: the return itself leaves the code
    /// with `returned`.
    pub resume: u64,
    pub witness_base: usize,
    /// The end of the innermost frame's hash witnesses. See Note [Hash witnesses].
    pub witness_top: usize,
    pub hash_witnesses: Witnesses,
    pub trap: bool,
    pub current_off: u16,
    /// What a return from JIT code leaves the JIT code with: where its caller
    /// continues (a `PackedLocation`), or -2 for a return from the entry
    /// frame. `PopFrame` writes it. See Note [Frame ops] in `specialize`.
    pub exit: u64,
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
    /// stay open. See Note [Captured slots] in `specialize`.
    pub fn close_upvalues(&mut self, owner: &mut Owner)
    {
        self.close_upvalues_from(owner, self.base)
    }

    /// Close every upvalue open into a slot from `from` up.
    pub fn close_upvalues_from(&mut self, owner: &mut Owner, from: usize)
    {
        let vals = &self.vals;
        self.upvals.retain(|(upval, uses)| {
            let Upvalue::Open(idx) = upval else { unreachable!("a closed upvalue in the open list") };
            if *idx < from {
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
        let at = self.base + a as usize;
        let len = self.vals.len();
        if c == 0 {
            // Every result, from the function's slot on, however many: the
            // stack is lengthened for them while the native runs (no GC runs
            // in a native), and back to where they end after.
            self.vals.lengthen(self.vals.capacity());
        }
        let args = &self.vals[at + 1..end];
        debug!("{:?}", args);
        let returns = if c == 0 {
            &self.vals[at..]
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
        // Taking every result, the caller reads up to the top; wanting `c - 1`,
        // the ones it didn't write are nil.
        if c == 0 {
            self.top = at + count;
            self.vals.truncate(len.max(self.top));
        } else {
            for slot in at + count.min(wanted)..at + wanted {
                self.vals[slot] = LBoxed::NIL;
            }
        }
    }

    // `extern "C"` so the JIT can call it directly. The callee closure is read
    // from slot `a` of the boxed stack, and the return location arrives packed
    // into a single word (a `PackedLocation`).
    pub extern "C" fn call_lua(&mut self, owner: &mut Owner,
        ret: PackedLocation, a: u16, b: u16) -> usize
    {
        let LValue::LClosure(lclos) = self.vals[self.base + a as usize].unbox() else { unreachable!() };
        let proto = unsafe { &*lclos.ro(owner).prototype };
        let (stack, vararg, params) = (proto.max_stack, proto.is_vararg != 0, proto.param_count as usize);
        let (a, b) = (a as usize, b as usize);
        // The arguments' end, before the frame is pushed.
        let passed = if b == 0 { self.top } else { self.base + a + b };
        let stack = self.push_frame(owner, ret, a, b, stack, true);
        if vararg {
            let func = self.base - 1;
            self.callstack.last_mut().expect("the frame just pushed").func = core::mem::MaybeUninit::new(func);
            self.move_past_varargs(passed, params, stack);
        }
        stack
    }

    /// Make the frame just pushed for a vararg function, whose arguments end at
    /// `passed`, start past them: the extra ones, past its `params` fixed ones,
    /// stay below it, and it starts with a copy of the fixed ones. See Note
    /// [Vararg frames].
    fn move_past_varargs(&mut self, passed: usize, params: usize, stack: usize) {
        let args = passed - self.base;
        if args <= params {
            return;
        }
        let base = passed;
        let end = base + stack;
        if end > self.vals.len() {
            self.vals.lengthen(end);
        }
        for i in 0..params {
            self.vals[base + i] = self.vals[self.base + i];
        }
        self.nil_slots(base + params, end);
        self.base = base;
        self.top = end;
    }

    /// `call_lua`, inlined into the window op pushing a frame in JIT code
    /// (`PushFrame`). See Note [Frame ops] in `specialize`.
    ///
    /// The callee's frame past its arguments is nil when it starts, as Lua's
    /// is: luac emits no LOADNIL for a local declared at a function's first
    /// instruction. With `fills`, this nils it; without, the caller does, before
    /// anything reads the stack or marks it. `stack` is the callee's
    /// `max_stack`, which the caller knows.
    #[inline(always)]
    pub fn push_frame(&mut self, owner: &mut Owner, ret: PackedLocation, a: usize, b: usize, stack: u8, fills: bool) -> usize {
        let LValue::LClosure(lclos) = self.vals[self.base + a].unbox() else { unreachable!() };
        debug_assert_eq!(stack, unsafe { (*lclos.ro(owner).prototype).max_stack }, "a call's frame size isn't its callee's");
        let ret_loc = Location::unpack(ret);
        // record call stack: we say where to return to and where to put the values
        let next_stack = stack as usize;
        let next_base = self.base + a + 1;
        // Its arguments are `b - 1` values, or up to the top, which the caller
        // wrote; the rest of its frame is nilled, so the stack only needs to be
        // long enough. See Note [Stack frames].
        let passed = if b == 0 { self.top } else { next_base + b - 1 };
        let end = next_base + next_stack;
        debug_assert!(passed <= self.vals.len(), "arguments past the stack");
        if end > self.vals.len() {
            self.vals.lengthen(end);
        }
        if fills && passed < end {
            self.nil_slots(passed, end);
        }
        self.callstack.push(CallstackEntry {
            clos: self.clos.clone(),
            ret: ret_loc,
            frame: self.base,
            // Set by `call_lua` if the function is vararg.
            func: core::mem::MaybeUninit::uninit(),
            witness_frame: self.witness_base,
            witness_top: self.witness_top,
        });
        self.base = next_base;
        // Start `top` at the end of the callee's register file.
        self.top = next_base + next_stack;
        self.witness_base = self.witness_top;
        self.clos = lclos.clone();
        next_stack
    }

    /// VARARG A B in the running frame, of a vararg function with `params`
    /// fixed parameters: its extra arguments to R(A) on, `b - 1` of them padded
    /// with nil, or with B = 0 all, the top just past them. See Note [Vararg
    /// frames].
    pub fn vararg(&mut self, owner: &Owner, a: usize, b: usize, params: usize) {
        debug_assert!(unsafe { (*self.clos.ro(owner).prototype).is_vararg } != 0, "VARARG in a function that isn't vararg");
        // The outermost frame, a chunk, has none.
        let extra = self.callstack.last().map_or(0, |entry| {
            // SAFETY: `entry` is the running frame's, and VARARG runs only in a
            // vararg function (asserted above), so it is a vararg function's
            // frame's entry, whose `func` `call_lua` set when pushing it.
            let func = unsafe { entry.vararg_func() };
            (self.base - func - 1).saturating_sub(params)
        });
        let (from, to) = (self.base - extra, self.base + a);
        let count = if b == 0 { extra } else { b - 1 };
        if to + count > self.vals.len() {
            self.vals.lengthen(to + count);
        }
        for i in 0..count {
            self.vals[to + i] = if i < extra { self.vals[from + i] } else { LBoxed::NIL };
        }
        if b == 0 {
            self.top = to + count;
        }
    }

    /// Nil the slots `from..to`. Out of line from `push_frame`: inlined, LLVM
    /// vectorizes the loop, and the window op pushing a frame (`PushFrame`)
    /// then ends in a `vzeroupper` on every call.
    #[inline(never)]
    fn nil_slots(&mut self, from: usize, to: usize) {
        for slot in from..to {
            self.vals[slot] = LBoxed::NIL;
        }
    }

    /// Move `count` results from `from` down to `to`. Out of line from
    /// `leave`, which moves one itself.
    #[inline(never)]
    fn move_down(&mut self, from: usize, count: usize, to: usize) {
        for i in 0..count {
            self.vals[to + i] = self.vals[from + i];
        }
    }

    /// Return from the running frame, the callee's half (Note [Returns]): close
    /// the frame's open upvalues, if its function can have opened any
    /// (`Residual::Ret`), pop it, and move its results, `b - 1` values from R(A)
    /// or every one up to the top, down to the slot the function was called
    /// from, the top just past them, for the caller to `arrive` at; then where
    /// the caller continues. From the outermost frame, instead the range of the
    /// stack its results are in, which the caller takes off it.
    ///
    /// Inlined into the window op popping a frame in JIT code (`PopFrame`). See
    /// Note [Frame ops] in `specialize`.
    #[inline(always)]
    pub fn leave(&mut self, owner: &mut Owner, a: usize, b: usize, closes: bool, vararg: bool) -> Result<Location, std::ops::Range<usize>> {
        debug_assert_eq!(unsafe { (*self.clos.ro(owner).prototype).is_vararg } != 0, vararg, "a return's vararg isn't its function's");
        if closes {
            if !self.upvals.is_empty() {
                self.close_upvalues(owner);
            }
        } else {
            debug_assert!(
                self.upvals.iter().all(|(upval, _)| matches!(upval, Upvalue::Open(idx) if *idx < self.base)),
                "an upvalue open into a frame whose function captures none of it"
            );
        }

        let from = self.base + a;
        let count = if b == 0 { self.top - from } else { b - 1 };
        match self.callstack.pop() {
            Some(entry) => {
                // The function's slot: a vararg function's frame's is recorded,
                // and any other's is just below its base. See Note [Vararg frames].
                let to = if vararg {
                    // SAFETY: `entry` is the returning frame's, whose function is
                    // vararg (`vararg`, asserted above), so `call_lua` set its
                    // `func` when pushing it.
                    unsafe { entry.vararg_func() }
                } else {
                    self.base - 1
                };
                let CallstackEntry { clos, ret, frame, witness_frame, witness_top, .. } = entry;
                match count {
                    0 => {},
                    1 => self.vals[to] = self.vals[from],
                    _ => self.move_down(from, count, to),
                }
                self.top = to + count;
                self.clos = clos;
                self.base = frame;
                self.witness_base = witness_frame;
                self.witness_top = witness_top;
                Ok(ret)
            },
            None => Err(from..from + count),
        }
    }

    /// TAILCALL A B in the running frame: close the frame's open upvalues, if
    /// its function can have opened any, and replace the frame with one for the
    /// Lua function in R(A), called with `b - 1` arguments, or every one up to
    /// the top. The new frame starts where the running one's function was, and
    /// returns where it would have; from the outermost frame, which has no slot
    /// for its function, the callee's arguments start at its base. `vararg` is
    /// whether the running function is vararg. The callee's `max_stack`. See
    /// Note [Tail calls] in `specialize`.
    ///
    /// Inlined into the window op replacing a frame in JIT code (`TailFrame`).
    /// See Note [Frame ops] in `specialize`.
    #[inline(always)]
    pub fn tail_call(&mut self, owner: &mut Owner, a: usize, b: usize, closes: bool, vararg: bool) -> usize {
        debug_assert_eq!(unsafe { (*self.clos.ro(owner).prototype).is_vararg } != 0, vararg, "a tail call's vararg isn't its function's");
        if closes {
            if !self.upvals.is_empty() {
                self.close_upvalues(owner);
            }
        } else {
            debug_assert!(
                self.upvals.iter().all(|(upval, _)| matches!(upval, Upvalue::Open(idx) if *idx < self.base)),
                "an upvalue open into a frame whose function captures none of it"
            );
        }
        let from = self.base + a;
        // The function and its arguments.
        let count = if b == 0 { self.top - from } else { b };
        let LValue::LClosure(lclos) = self.vals[from].unbox() else { unreachable!("a tail call of what isn't a Lua function") };
        let proto = unsafe { &*lclos.ro(owner).prototype };
        let (stack, callee_vararg, params) = (proto.max_stack as usize, proto.is_vararg != 0, proto.param_count as usize);
        let next_base = match self.callstack.last() {
            Some(entry) => {
                // The function's slot, as `leave` finds it. See Note [Vararg frames].
                let func = if vararg {
                    // SAFETY: `entry` is the running frame's, whose function is vararg
                    // (asserted above), so `call_lua` set its `func` when pushing it.
                    unsafe { entry.vararg_func() }
                } else {
                    self.base - 1
                };
                self.move_down(from, count, func);
                func + 1
            },
            None => {
                assert!(!callee_vararg, "not implemented: a tail call of a vararg function from the outermost frame");
                self.move_down(from + 1, count - 1, self.base);
                self.base
            },
        };
        let passed = next_base + count - 1;
        let end = next_base + stack;
        if end > self.vals.len() {
            self.vals.lengthen(end);
        }
        if passed < end {
            self.nil_slots(passed, end);
        }
        self.base = next_base;
        self.top = end;
        // The running frame's hash witnesses are the callee's to reuse.
        self.witness_top = self.witness_base;
        self.clos = lclos.clone();
        // The frame's entry records its function's slot if it is vararg. See Note
        // [Vararg frames].
        if let Some(entry) = self.callstack.last_mut() {
            entry.func = if callee_vararg { core::mem::MaybeUninit::new(next_base - 1) } else { core::mem::MaybeUninit::uninit() };
        }
        if callee_vararg {
            self.move_past_varargs(passed, params, stack);
        }
        stack
    }

    /// Take the results of the call of R(A) that returned (`leave`), the
    /// caller's half (Note [Returns]): exactly `c - 1`, padded with nil, or
    /// with C = 0 all of them, up to the top.
    ///
    /// Inlined into the window op for a call's results in JIT code (`Arrive`).
    #[inline(always)]
    pub fn arrive(&mut self, a: usize, c: usize) {
        let at = self.base + a;
        debug_assert!(self.top >= at, "results below the call");
        if c != 0 {
            let end = at + c - 1;
            match c - 1 {
                0 => {},
                1 => if self.top == at { self.vals[at] = LBoxed::NIL },
                _ => if self.top < end { self.nil_slots(self.top, end) },
            }
            self.top = end;
        }
    }

    /// The stack's live extent, which the GC marks: the most of each live
    /// frame's `base + max_stack`, the running one's and each caller's, and of
    /// the top. See Note [Stack frames].
    pub fn live_extent(&self, owner: &Owner) -> usize {
        let end = |base: usize, clos: &Tc<LClosure<'src, 'intern>>| base + unsafe { (*clos.ro(owner).prototype).max_stack as usize };
        let running = end(self.base, &self.clos).max(self.top);
        let extent = self.callstack.iter().map(|call| end(call.frame, &call.clos)).fold(running, usize::max);
        debug_assert!(extent <= self.vals.len(), "a live frame past the stack");
        extent
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
        // Past the live extent the stack goes, before the GC can free what its
        // slots name. See Note [Stack frames].
        let extent = self.live_extent(owner);
        for val in &self.vals[..extent] {
            val.mark(owner);
        }
        self.vals.truncate(extent);
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
        #[cfg(feature = "tracing")]
        crate::tracing::init("lunacy.fxt");
        Self { top_level }
    }

    /// A prototype's source and the line it's defined at.
    pub fn info(proto: LProto<'src, 'intern>) -> (String, u32) {
        unsafe {
            let source = String::from_utf8_lossy((*proto).source.data).to_string().replace("\0", "");
            (source, (*proto).line_defined)
        }
    }

    pub(crate) fn global_env(&self, intern: &'intern internment::Arena<IStr<'src>>) -> Tc<Table<'src, 'intern>> {
        let mut math_tab = Table::new(0, 0);
        // Unary float builtins consume the boxed stack directly: decode the one
        // argument with `as_number()` and write the result back as a boxed double.
        math_tab.insert_lvalue(InternString::intern(intern, "huge"), LValue::NClosure(NClosure::new(|mut seq, args, returns, _owner|{
            returns.rw(&mut seq).into_iter().next().map(|r| *r = LBoxed::from_number(f64::INFINITY));
            1
        })));
        math_tab.insert_lvalue(InternString::intern(intern, "pi"), LValue::number(std::f64::consts::PI));
        for (name, native) in crate::library::math_natives() {
            math_tab.insert_lvalue(InternString::intern(intern, name), native);
        }

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
                        b"collect" | b"" => { unsafe { GcCtx::assume_rooted().full_collect_published(owner); } LValue::number(0.0) },
                        // Live memory in Kbytes, as a (fractional) number.
                        b"count" => LValue::number(Heap::live_bytes() as f64 / 1024.0),
                        // Advance one incremental step.
                        b"step" => { unsafe { GcCtx::assume_rooted().step_published(owner); } LValue::Bool(false) },
                        b"stop" => { Heap::set_gc_off(true); LValue::number(0.0) },
                        b"restart" => { Heap::set_gc_off(false); LValue::number(0.0) },
                        // Tuning knobs we accept but don't model.
                        b"setpause" | b"setstepmul" => LValue::number(0.0),
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
            kind: 0,
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
        #[cfg(feature = "tracing")]
        crate::tracing::begin("interpreter", "run", &[]);
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
                cold_site: core::ptr::null(),
                returned: 0,
                resume: 0,
                witness_base,
                witness_top: 0,
                pc,
                _G,
                clos,
                vals,
                upvals,
                callstack,
                counters: Default::default(),
                hash_witnesses: Witnesses::new(),
                select: 0,
                trap: false,
                #[cfg(feature = "magic")]
                force_jit: vec![].into(),
                current_off: 0,
                exit: 0,
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
        #[cfg(feature = "tracing")]
        {
            spec.trace_blocks(owner);
            crate::tracing::end("interpreter", "run", &[]);
            crate::tracing::flush();
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
