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

#[cfg(feature = "lbbv")]
use crate::generator::{Specializer, Context, SubPc};

// `BlockId` and `HashRef` are referenced by `ReturnLocation` / `HashWitness`,
// which exist in every build, so they live here rather than in the
// lbbv-gated generator module (which re-imports them).
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash, Debug)]
pub struct BlockId(pub usize);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HashRef(pub u8);
use crate::perf::PerfCounters;
use crate::gc::{Mark, Heap, Gc, GcCtx};
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
    pub hash: IndexMap<LCanon<'src, 'intern>, LBoxed<'src, 'intern>, InternedHasher>,
    pub epoch: usize,
}

impl<'src, 'intern> Table<'src, 'intern> {
    pub fn new(array: usize, hash: usize) -> Self {
        Self {
            array: vec![LBoxed::NIL; array].into(),
            hash: IndexMap::with_capacity_and_hasher(hash, InternedHasher::default()),
            epoch: 0,
        }
    }

    /// Insert a key/value without an intern arena to canonicalize the key (unlike
    /// `set`/`get`). Valid only for builtin keys, which are already interned strings
    /// and so satisfy the canonical-form invariant of Note [Canonical values] directly.
    pub fn insert_lvalue(&mut self, key: LValue<'src, 'intern>, value: LValue<'src, 'intern>) {
        self.hash.insert(LCanon(LBoxed::box_lvalue(key)), LBoxed::box_lvalue(value));
    }
}

impl<'src, 'intern> Tc<Table<'src, 'intern>> {
    /// Fire the table write barrier before mutating this table's array/hash in place.
    /// See Note [Write barriers].
    #[inline]
    pub fn barrier_back(&self) {
        self.0.backward_barrier();
    }

    /// Look up a key. Numbers index the array part; everything else goes through
    /// the hash part as an `LCanon`. See Note [Canonical values].
    #[inline]
    pub fn get(&self, owner: &Owner, key: &LBoxed<'src, 'intern>, intern: &'intern internment::Arena<IStr<'src>>) -> Option<LBoxed<'src, 'intern>> {
        if let Some(n) = key.as_number() {
            return Some(self.ro(owner).array.get(n as usize - 1).copied().unwrap_or(LBoxed::NIL));
        }
        let k = LCanon::new(*key, intern);
        self.ro(owner).hash.get(&k).copied()
    }

    #[inline]
    pub fn set(&mut self, owner: &mut Owner, key: LBoxed<'src, 'intern>, value: LBoxed<'src, 'intern>, intern: &'intern internment::Arena<IStr<'src>>) {
        self.barrier_back();
        if let Some(n) = key.as_number() {
            // TODO: sparse arrays
            let n = n as usize;
            if self.rw(owner).array.len() < n {
                self.rw(owner).array.resize_with(n, || LBoxed::NIL);
            }
            self.rw(owner).array[n - 1] = value;
            return;
        }
        let k = LCanon::new(key, intern);
        self.rw(owner).hash.insert(k, value);
        self.rw(owner).epoch += 1;
    }
}

#[repr(u8)]
#[derive(Hash, Clone)]
pub enum InternString<'intern, 'src> {
    Interned(ArenaIntern<'intern, IStr<'src>>),
    Owned(Gc<FVec<u8>>),
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
                self_o.partial_cmp(other_o)
            }
        }
    }
}

impl<'intern, 'src> Eq for InternString<'intern, 'src> { }

impl<'intern, 'src> Debug for InternString<'intern, 'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InternString::Interned(i) => write!(f, "{}", String::from_utf8_lossy(i.as_bytes())),
            InternString::Owned(o) => write!(f, "{}", String::from_utf8_lossy(o)),
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
            InternString::Owned(o) => o.as_ref(),
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
    // plain `Gc<FVec<u8>>` (not `Tc`) lets their bytes be read without an
    // `owner`, which is what makes content-based equality/hashing possible.
    OwnedString(Gc<FVec<u8>>) = 5,
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
impl crate::gc::CellKind for FVec<u8> {
    fn cell_kind() -> u8 { LBoxed::KIND_OWNED }
}

// Note [Canonical values]
// ~~~~~~~~~~~~~~~~~~~~~~~~~
// `LCanon` is an `LBoxed` in canonical form: equal values have identical bits, so it
// implements `Hash`/`Eq` by value — comparing the raw bits, pointers included — with no
// `owner`. `LCanon::new` does the canonicalizing: an owned string is interned, which the
// arena dedups to the one pointer shared by every string with those bytes. Everything
// else is already canonical: interned strings are that unique pointer, tables/closures
// compare by identity, and numbers/bool/nil are their own bits.
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
            _ => LCanon(v),
        }
    }

    #[inline(always)]
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
                        Ok(LValue::Number(Number(left_n.0 % right_n.0))),
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

    pub fn as_string(&self, owner: &Owner) -> Option<Gc<FVec<u8>>> {
        // TODO: metamethods?
        match self {
            LValue::OwnedString(s) => Some(s.clone()),
            LValue::InternedString(s) => Some(Gc::new(s.into_ref().as_bytes().to_vec().into())),
            LValue::Number(f) => {
                let mut s: FVec<_> = vec![].into();
                write!(s, "{}", f.0);
                Some(Gc::new(s))
            },
            LValue::Table(tc) => {
                let mut s: FVec<_> = vec![].into();
                write!(s, "{:?}", tc);
                Some(Gc::new(s))
            },
            LValue::Nil => {
                let mut s: FVec<_> = vec![].into();
                write!(s, "nil");
                Some(Gc::new(s))

            },
            LValue::LClosure(l) => {
                let mut s: FVec<_> = vec![].into();
                let line = unsafe { (*l.0.ro(owner).prototype).line_defined };
                let src = unsafe { &(*l.0.ro(owner).prototype).source };
                write!(s, "function({:p}, {:?} @ {})", l.as_ptr(), src, line);
                Some(Gc::new(s))
            },
            LValue::NClosure(nf) => {
                let mut s: FVec<_> = vec![].into();
                write!(s, "native({:p})", nf.native());
                Some(Gc::new(s))
            },
            x => unimplemented!("{:?}", x),
        }
    }

    pub fn as_string_nolock(&self) -> Option<Gc<FVec<u8>>> {
        // TODO: metamethods?
        match self {
            LValue::OwnedString(s) => Some(s.clone()),
            LValue::InternedString(s) => Some(Gc::new(s.into_ref().as_bytes().to_vec().into())),
            LValue::Number(f) => {
                let mut s: FVec<_> = vec![].into();
                write!(s, "{}", f.0);
                Some(Gc::new(s))
            },
            LValue::Table(tc) => {
                let mut s: FVec<_> = vec![].into();
                write!(s, "{:?}", tc);
                Some(Gc::new(s))
            },
            LValue::Nil => None,
            LValue::LClosure(l) => {
                let mut s: FVec<_> = vec![].into();
                write!(s, "function({:p})", l.as_ptr());
                Some(Gc::new(s))
            },
            x => unimplemented!("{:?}", x),
        }
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

pub type NativeFunc = for<'id, 'a, 'src, 'intern> fn(LCellOwner<'id>, &'a LCell<'id, [LBoxed<'src, 'intern>]>, &'a LCell<'id, [LBoxed<'src, 'intern>]>, &mut Owner);
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

    /// Enter the interpreter — the only way in, since `Vm::run` is crate-private. See Note
    /// [Scoped heap].
    #[inline]
    pub fn run<const LBBV: bool>(
        &self,
        owner: &mut Owner,
        _G: Tc<Table<'gc, 'gc>>,
        clos: Tc<LClosure<'gc, 'gc>>,
        args: ValueStack<'gc, 'gc>,
    ) -> Result<FVec<LValue<'gc, 'gc>>, Box<dyn Error>> {
        self.vm().run::<LBBV>(self.gc, owner, _G, clos, args, self.intern())
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

#[derive(Debug)]
pub enum ReturnLocation {
    Interpreter(usize),
    Generator(BlockId, usize),
}

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
    /// without passing a `repr(Rust)` enum by value. Bit 63 selects the variant;
    /// `Generator` packs `(off << 32) | block` in the low bits (the same layout the
    /// JIT's `lua_return` already uses for its return encoding).
    pub fn pack(self) -> PackedLocation {
        PackedLocation(match self {
            ReturnLocation::Interpreter(pc) => pc,
            ReturnLocation::Generator(BlockId(block), off) => (1usize << 63) | (off << 32) | block,
        })
    }

    pub fn unpack(p: PackedLocation) -> Self {
        let p = p.0;
        if (p >> 63) == 1 {
            ReturnLocation::Generator(BlockId(p & 0xffff_ffff), (p >> 32) & 0x7fff_ffff)
        } else {
            ReturnLocation::Interpreter(p)
        }
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
pub struct CallstackEntry<'src, 'intern> { pub clos: Tc<LClosure<'src, 'intern>>, pub ret: ReturnLocation, pub frame: usize, pub limit: usize, pub witness_frame: usize, pub witness_limit: usize, pub rloc: usize, pub c: u16 }

#[derive(Debug)]
pub struct HashWitness {
    pub href: HashRef,
    pub key: LConstant<'static, 'static>,
    pub index: usize,
    pub epoch: usize,
}

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
    pub hash_witnesses: FVec<Option<HashWitness>>,
    pub trap: bool,
    pub current_off: u16,
    pub gas: i64,
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
    pub fn close_upvalues(&mut self, owner: &mut Owner)
    {
        for upval in self.upvals.iter() {
            let idx = match &upval.0 {
                Upvalue::Open(o) => o,
                Upvalue::Closed(u) => panic!(), // we shouldn't have any closed upvals
            };
            // migrate all the stack references to be GC references, since we're
            // going to be removing it from the stack
            let closed = Tc::new(self.vals[*idx].clone());
            for up_use in upval.1.iter() {
                up_use.replace(owner, Upvalue::Closed(closed.clone()));
            }
        }
    }

    #[inline(always)]
    // Natives take `LBoxed` slice views over the arg/return stack regions, so the
    // boxed stack is aliased in place with no unbox/rebox copy.
    pub fn call_native(&mut self, nf: NativeFunc, a: u16, b: u16, c: u16, owner: &mut Owner) {
        let args = if b == 0 {
            &self.vals[self.base + a as usize+1..self.top]
        } else {
            &self.vals[self.base + a as usize+1..=(self.base + a as usize + b as usize - 1)]
        };
        debug!("{:?}", args);
        let returns = if c == 0 {
            // save all returned
            &self.vals[self.base + a as usize..self.top]
        }
        else if c == 1 {
            // nothing saved
            &[]
        } else if c >= 2 {
            &self.vals[self.base + a as usize..=self.base + a as usize + c as usize - 2]
        } else {
            unimplemented!()
        };
        LCellOwner::scope(|mut seq| {
            // Safety: LCellOwner guarantees that the native function can only ever
            // have mutable access to one slice at a time. The transmute wraps the
            // aliased stack slices in-place as `LCell`s (repr(transparent) over UnsafeCell).
            let args = unsafe { core::mem::transmute(seq.cell(args)) };
            let returns = unsafe { core::mem::transmute(seq.cell(returns)) };
            let ret = (nf)(seq, args, returns, owner);
        });
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
        // The callee's frame extends the live max-extent while it runs.
        self.natural_max = self.natural_max.max(next_base + next_stack);
        self.callstack.push(CallstackEntry {
            clos: self.clos.clone(),
            ret: ret_loc,
            frame: self.base,
            limit,
            rloc: self.base + a as usize,
            witness_frame: self.witness_base,
            witness_limit: self.hash_witnesses.len(),
            c
        });
        self.base = next_base;
        // Start `top` at the end of the callee's register file.
        self.top = next_base + next_stack;
        self.witness_base = self.hash_witnesses.len();
        self.clos = lclos.clone();
        next_stack
    }

    pub fn do_return(&mut self, owner: &mut Owner, a: usize, b: usize) -> Result<ReturnLocation, FVec<LBoxed<'src, 'intern>>> {
        // we're going to be removing this frame, so close any open
        // upvalues.
        self.close_upvalues(owner);
        self.upvals.truncate(0);

        let mut r_count = 0 as usize;
        let mut r_vals: FVec<_> = if b == 1 {
            // no return values
            vec![].into()
        } else if b >= 2 {
            // there are b-1 return values from R(A) onwards
            r_count = b as usize-1;
            let r_vals = &self.vals[self.base + a as usize..(self.base + a as usize + r_count as usize)];
            debug!("{:?}", r_vals);
            Vec::from(r_vals).into()
        } else if b == 0 {
            // return all values from R(A) to the current top
            let r_vals = &self.vals[self.base + a as usize..self.top];
            r_count = r_vals.len() as usize;
            debug!("{:?}", r_vals);
            Vec::from(r_vals).into()
        } else {
            unreachable!()
        };
        match self.callstack.pop() {
            Some(CallstackEntry { clos: ret_clos, ret, frame, limit, witness_frame, witness_limit, rloc, c }) => {
                debug!("{} {:?} {}", self.base, unsafe { &(*ret_clos.ro(owner).prototype).instructions }, c);
                self.clos = ret_clos.clone();
                self.base = frame;
                self.witness_base = witness_frame;
                // The callee frame is gone; the live max-extent is the caller's again.
                self.natural_max = limit;
                // Shrink the register file back to the caller's extent (`limit`) so the
                // popped callee frame stops being marked by the GC. See Note [Stack frames].
                if c == 1 {
                    // results discarded
                    self.top = rloc;
                    self.vals.truncate(limit);
                } else if c >= 2 {
                    // exactly c-1 results, padded with nil
                    for i in 0..(c as usize - 1) {
                        self.vals[rloc + i] = r_vals.get(i).copied().unwrap_or(LBoxed::NIL);
                    }
                    self.top = rloc + (c as usize - 1);
                    self.vals.truncate(limit);
                } else {
                    // MULTRET: every returned value, which can exceed `limit` when the
                    // callee returned more than the caller's extent covers.
                    for (i, v) in r_vals.drain(..).enumerate() {
                        self.vals[rloc + i] = v;
                    }
                    self.top = rloc + r_count;
                    self.vals.truncate(limit.max(rloc + r_count));
                }
                self.hash_witnesses.truncate(witness_limit);
                return Ok(ret)
            },
            None => {
                self.vals.truncate(0);
                Err(r_vals)
            }
        }
    }
}

impl<'src, 'intern> Mark for RunState<'src, 'intern> {
    fn mark(&self, owner: &Owner) {
        for val in self.vals.iter() {
            val.mark(owner);
        }
        self.clos.mark(owner);
        self._G.mark(owner);
        for upval in self.upvals.iter() {
            // We only need to mark closed upvalues, because open ones were marked on the value
            // stack.
            if let Upvalue::Closed(o) = &upval.0 {
                o.mark(owner);
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
                }))
            };
        }
        math_tab.insert_lvalue(InternString::intern(intern, "floor"), math1!(f64::floor));
        math_tab.insert_lvalue(InternString::intern(intern, "ceil"), math1!(f64::ceil));
        math_tab.insert_lvalue(InternString::intern(intern, "sqrt"), math1!(f64::sqrt));
        math_tab.insert_lvalue(InternString::intern(intern, "abs"), math1!(f64::abs));
        math_tab.insert_lvalue(InternString::intern(intern, "huge"), LValue::NClosure(NClosure::new(|mut seq, args, returns, _owner|{
            returns.rw(&mut seq).into_iter().next().map(|r| *r = LBoxed::from_number(f64::INFINITY));
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
                    // No returns
                }))),
                (InternString::intern(intern, "assert"), LValue::NClosure(NClosure::new(|seq, args, _returns, _owner| {
                    if let [b, ..] = args.ro(&seq) {
                        if let LValue::Bool(false) = b.unbox() {
                            panic!("lua assert failed");
                        }
                    }
                    // No returns
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
                }))),
                math,
                os,
                ].drain(..).map(|(k, v)| (LCanon(LBoxed::box_lvalue(k)), LBoxed::box_lvalue(v)))
            ),
            epoch: 0,
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

    /// The interpreter entry, gated behind the scope's `GcCtx` token. Crate-private so the only
    /// way in is [`Scoped::run`]. See Note [Scoped heap].
    pub(crate) fn run<'lua, 'gc, const LBBV: bool>(&'lua self,
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

        #[cfg(feature = "lbbv")]
        let mut spec = Specializer::new(clos.clone());
        // Interpreter-only builds have no generator to trace; the GC safepoints
        // still take a "spec" root, so bind a no-op `()` (Mark's default is a
        // trivial no-op for non-drop types).
        #[cfg(not(feature = "lbbv"))]
        let spec = ();
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
                current_off: 0,
                gas: std::env::var("LUNACY_GAS").ok().and_then(|v| v.parse().ok()).unwrap_or(i64::MAX),
                intern,
            }
        };
        // `gc` is the scope's rooting token, threaded in by `Scoped::run`; the rooting scope
        // stays live for the whole `Vm::scope`. See Note [GC roots].
        // we need to track where to return to, along with the base pointer and where to put return
        // values
        let r_vals = 'int: loop {
            // SAFETY: at instruction boundaries every live GC value is in the RunState.
            #[cfg(feature = "gc_stress")]
            unsafe { gc.step(&state, &spec, owner); }

            let inst = unsafe { state.clos.ro(owner).prototype.as_ref().unwrap().instructions.items[state.pc] };
            state.pc += 1;
            state.counters.interpreter_count.increment();
            debug!("pc {} inst {:?}", state.pc, inst.0.Opcode());
            debug!("stack: {}, {:?}", state.base, &state.vals);
            match inst.0.Opcode() {
                Opcode::MOVE => {
                    let (a, b) = <MOVE as InstructionDecode>::Unpack::unpack(inst.0);
                    debug!("move {} {}", a, b);
                    state.vals[state.base + a as usize] = state.vals[state.base + b as usize].clone();
                },
                Opcode::GETUPVAL => {
                    let (a, b) = <GETUPVAL as InstructionDecode>::Unpack::unpack(inst.0);
                    let upval = match state.clos.ro(owner).upvalues[b as usize].ro(owner) {
                        Upvalue::Open(o) => {
                            state.vals[*o as usize].clone()
                        },
                        Upvalue::Closed(c) => {
                            c.ro(owner).clone()
                        },
                    };
                    state.vals[state.base + a as usize] = upval.clone();
                },
                Opcode::SETUPVAL => {
                    let (a, b) = <SETUPVAL as InstructionDecode>::Unpack::unpack(inst.0);
                    let upval = match state.clos.ro(owner).upvalues[b as usize].ro(owner) {
                        Upvalue::Open(o) => {
                            state.vals[*o as usize] = state.vals[state.base + a as usize].clone()
                        },
                        Upvalue::Closed(c) => {
                            let c = c.clone();
                            let new_val = state.vals[state.base + a as usize].clone();
                            c.replace(owner, new_val);
                        },
                    };
                },
                Opcode::LOADK => {
                    let (a, bx) = <LOADK as InstructionDecode>::Unpack::unpack(inst.0);
                    debug!("loadk {} {} {:?}", a, bx, unsafe { &(&(*state.clos.ro(owner).prototype).constants.items)[bx as usize] });
                    state.vals[state.base + a as usize] = unsafe { (&(&(*state.clos.ro(owner).prototype).constants.items)[bx as usize]).into() };
                    ()
                },
                Opcode::LOADNIL => {
                    let (a, b) = <LOADNIL as InstructionDecode>::Unpack::unpack(inst.0);
                    state.vals[state.base + a as usize..=state.base + b as usize].iter_mut().for_each(|i| *i = LBoxed::NIL);
                    ()
                },
                Opcode::LOADBOOL => {
                    let (a, b, c) = <LOADBOOL as InstructionDecode>::Unpack::unpack(inst.0);
                    state.vals[state.base + a as usize] = LBoxed::from_bool(b != 0);
                    if c != 0 {
                        state.pc += 1;
                    }
                    ()
                },
                Opcode::NEWTABLE => {
                    let (a, b, c) = <NEWTABLE as InstructionDecode>::Unpack::unpack(inst.0);
                    // TODO: properly decode the "floating point byte" size hints instead
                    state.vals[state.base + a as usize] = LBoxed::box_lvalue(LValue::Table(Tc::new(Table::new(b as usize, c as usize))));
                    // SAFETY: the newly created table is reachable through the RunState.
                    unsafe { gc.step(&state, &spec, owner); }
                },
                Opcode::SELF => {
                    let (a, b, c) = <SELF as InstructionDecode>::Unpack::unpack(inst.0);
                    let rb = state.vals[state.base + b as usize];
                    state.vals[state.base + a as usize + 1] = rb;
                    let key = Self::rk_boxed(Self::rk(state.clos.ro(owner).prototype, state.base, &state.vals, c));
                    let tab = rb.as_table().unwrap_or_else(|| unimplemented!("self on non-table"));
                    state.vals[state.base + a as usize] = tab.get(owner, &key, state.intern).unwrap_or(LBoxed::NIL);
                },
                Opcode::SETLIST => {
                    let (a, b, c) = <SETLIST as InstructionDecode>::Unpack::unpack(inst.0);
                    let tab = state.vals[state.base + a as usize].as_table().unwrap_or_else(|| unimplemented!("setlist on non-table"));
                    assert_ne!(c, 0);
                    tab.barrier_back();
                    let start = state.base + a as usize + 1;
                    let end = if b == 0 { state.top } else { start + b as usize };
                    let src: Vec<LBoxed> = state.vals[start..end].iter().copied().collect();
                    tab.rw(owner).array.splice((c as usize-1)*50.., src).for_each(drop);
                },
                Opcode::GETTABLE => {
                    let (a, b, c) = <GETTABLE as InstructionDecode>::Unpack::unpack(inst.0);
                    debug!("gettable {} {} {}", a, b, c);
                    let key = Self::rk_boxed(Self::rk(state.clos.ro(owner).prototype, state.base, &state.vals, c));
                    let tab = state.vals[state.base + b as usize].as_table().unwrap_or_else(|| unimplemented!("gettable on non-table"));
                    state.vals[state.base + a as usize] = tab.get(owner, &key, state.intern).unwrap_or(LBoxed::NIL);
                },
                Opcode::SETTABLE => {
                    let (a, b, c) = <SETTABLE as InstructionDecode>::Unpack::unpack(inst.0);
                    debug!("settable {} {} {}", a, b, c);
                    let kb = Self::rk_boxed(Self::rk(state.clos.ro(owner).prototype, state.base, &state.vals, b));
                    let kc = Self::rk_boxed(Self::rk(state.clos.ro(owner).prototype, state.base, &state.vals, c));
                    let target = state.vals[state.base + a as usize];
                    if let Some(mut tab) = target.as_table() {
                        tab.set(owner, kb, kc, state.intern);
                    } else {
                        // Handle magic debugging keys (`t.__jit = ...` forces JIT
                        // compilation). Meaningful only in JIT builds; in the
                        // interpreter it is a no-op.
                        // Forcing JIT compilation only means anything with the
                        // native code generator; it reaches into `jit_info`,
                        // which only exists under `jit`.
                        #[cfg(feature = "jit")]
                        if let (LValue::LClosure(lc), LValue::InternedString(key)) = (target.unbox(), kb.unbox()) {
                            match key.as_bytes() {
                                x if x == const { "__jit".as_bytes() } => {
                                    if let Entry::Occupied(mut entry) = spec.versions.entry(lc.rw(owner).prototype) {
                                        for block in entry.get_mut().values() {
                                            warn!("Forcing JIT for block {}", block.0);
                                            spec.blocks[block.0].jit_info.hotness.set(0);
                                        }
                                    }
                                },
                                _ => unimplemented!(),
                            }
                        } else {
                            unimplemented!()
                        }
                        // Without the JIT there is nothing to force; treat
                        // `closure.__jit = ...` as a no-op (matching the JIT
                        // build's behaviour when no blocks are versioned).
                        #[cfg(not(feature = "jit"))]
                        if let (LValue::LClosure(_), LValue::InternedString(key)) = (target.unbox(), kb.unbox()) {
                            match key.as_bytes() {
                                x if x == const { "__jit".as_bytes() } => {},
                                _ => unimplemented!(),
                            }
                        } else {
                            unimplemented!()
                        }
                    }
                },
                Opcode::SETGLOBAL => {
                    let (a, bx) = <SETGLOBAL as InstructionDecode>::Unpack::unpack(inst.0);
                    let kst = unsafe { &(&(*state.clos.ro(owner).prototype).constants.items)[bx as usize] };
                    debug!("setglobal {} {} {:?}", a, bx, &kst);
                    state._G.set(owner, kst.into(), state.vals[state.base + a as usize].clone(), state.intern);
                },
                Opcode::GETGLOBAL => {
                    let (a, bx) = <GETGLOBAL as InstructionDecode>::Unpack::unpack(inst.0);
                    let kst = unsafe { &(&(*state.clos.ro(owner).prototype).constants.items)[bx as usize] };
                    debug!("getglobal {} {} {:?}", a, bx, &kst);
                    // FIXME(error handling)
                    state.vals[state.base + a as usize] = state._G.get(owner, &kst.into(), state.intern).unwrap_or((&Constant::Nil).into()).clone();
                },
                Opcode::TEST => {
                    let (a, _, c) = <TEST as InstructionDecode>::Unpack::unpack(inst.0);
                    // R(A) truthiness compared against C, straight off the bits.
                    if state.vals[state.base + a as usize].truthy() == (c != 0) {
                        // No-op
                    } else {
                        state.pc += 1;
                    }
                },
                opcode @ (Opcode::EQ | Opcode::LT | Opcode::LE) => {
                    let (a, b, c) = ABC::unpack(inst.0);
                    let kb = Self::rk(state.clos.ro(owner).prototype, state.base, &state.vals, b);
                    let kc = Self::rk(state.clos.ro(owner).prototype, state.base, &state.vals, c);
                    // Numeric fast path: pull both operands out as f64 without
                    // ever building an `LValue`.
                    let bn = match kb { Ok(Constant::Number(n)) => Some(n.0), Ok(_) => None, Err(lb) => lb.as_number() };
                    let cn = match kc { Ok(Constant::Number(n)) => Some(n.0), Ok(_) => None, Err(lb) => lb.as_number() };
                    let cond = if let (Some(x), Some(y)) = (bn, cn) {
                        match opcode {
                            Opcode::EQ => x == y,
                            Opcode::LT => x < y,
                            Opcode::LE => x <= y,
                            _ => unsafe { std::hint::unreachable_unchecked() },
                        }
                    } else {
                        // Fallback (strings / other): decode to the view type.
                        let lb = match kb { Ok(c) => LValue::from(c), Err(v) => v.unbox() };
                        let lc = match kc { Ok(c) => LValue::from(c), Err(v) => v.unbox() };
                        lb.compare(opcode, lc, owner).unwrap()
                    };
                    if (cond as u8) != a {
                        state.pc += 1;
                    }
                },
                opcode @ (Opcode::ADD | Opcode::SUB | Opcode::MUL | Opcode::DIV | Opcode::MOD | Opcode::POW)
                => {
                    let (a, b, c) = ABC::unpack(inst.0);
                    let kb = Self::rk(state.clos.ro(owner).prototype, state.base, &state.vals, b);
                    let kc = Self::rk(state.clos.ro(owner).prototype, state.base, &state.vals, c);
                    let bn = match kb { Ok(Constant::Number(n)) => Some(n.0), Ok(_) => None, Err(lb) => lb.as_number() };
                    let cn = match kc { Ok(Constant::Number(n)) => Some(n.0), Ok(_) => None, Err(lb) => lb.as_number() };
                    let res = if let (Some(x), Some(y)) = (bn, cn) {
                        // Numeric fast path: compute in f64 and re-box directly.
                        let r = match opcode {
                            Opcode::ADD => x + y,
                            Opcode::SUB => x - y,
                            Opcode::MUL => x * y,
                            Opcode::DIV => x / y,
                            Opcode::MOD => x % y,
                            Opcode::POW => x.powf(y),
                            _ => unsafe { std::hint::unreachable_unchecked() },
                        };
                        LBoxed::from_number(r)
                    } else {
                        // Fallback (metamethods / coercions): decode to the view type.
                        let lb = match kb { Ok(c) => LValue::from(c), Err(v) => v.unbox() };
                        let lc = match kc { Ok(c) => LValue::from(c), Err(v) => v.unbox() };
                        LBoxed::box_lvalue(lb.numeric_op(opcode, &lc)?)
                    };
                    state.vals[state.base + a as usize] = res;
                },
                Opcode::UNM => {
                    let (a, b) = <UNM as InstructionDecode>::Unpack::unpack(inst.0);
                    // TODO: metatables
                    let n = state.vals[state.base + b as usize].as_number().unwrap_or_else(|| unimplemented!("unm on non-number"));
                    state.vals[state.base + a as usize] = LBoxed::from_number(-n);
                },
                Opcode::LEN => {
                    let (a, b) = <LEN as InstructionDecode>::Unpack::unpack(inst.0);
                    debug!("{} {}", a, b);
                    let res = state.vals[state.base + b as usize].unbox().len(owner)?;
                    state.vals[state.base + a as usize] = LBoxed::box_lvalue(res);
                },
                Opcode::CONCAT => {
                    let (a, b, c) = <CONCAT as InstructionDecode>::Unpack::unpack(inst.0);
                    debug!("{} {}", a, b);
                    let mut s: FVec<_> = vec![].into();
                    for i in (b as usize)..=(c as usize) {
                        let val = state.vals[state.base + i as usize].unbox();
                        s.extend_from_slice(val.as_string(owner).ok_or("nil concat")?.as_slice())
                    }
                    debug!("concat {:?}", String::from_utf8_lossy(s.as_slice()));
                    // Concat stays cheap: the result is an owned string, not
                    // interned. It only gets canonicalized if/when used as a
                    // table key (via `LCanon`).
                    state.vals[state.base + a as usize] = LBoxed::box_lvalue(LValue::OwnedString(Gc::new(s)));
                },
                Opcode::FORPREP => {
                    let (a, sbx) = <FORPREP as InstructionDecode>::Unpack::unpack(inst.0);
                    debug!("{} {}", a, sbx);
                    let init = state.vals[state.base + a as usize].as_number().expect("forprep index non-number");
                    let step = state.vals[state.base + a as usize + 2].as_number().expect("forprep step non-number");
                    state.vals[state.base + a as usize] = LBoxed::from_number(init - step);
                    state.pc += sbx as usize;
                },
                Opcode::FORLOOP => {
                    let (a, sbx) = <FORLOOP as InstructionDecode>::Unpack::unpack(inst.0);
                    debug!("{} {}", a, sbx);
                    // Hot numeric loop: step / index / limit are always numbers.
                    let step = state.vals[state.base + a as usize + 2].as_number().expect("forloop step non-number");
                    let idx = state.vals[state.base + a as usize].as_number().expect("forloop index non-number") + step;
                    state.vals[state.base + a as usize] = LBoxed::from_number(idx);
                    let limit = state.vals[state.base + a as usize + 1].as_number().expect("forloop limit non-number");
                    let comp = if step < 0.0 { limit <= idx } else { idx <= limit };
                    if comp {
                        state.pc = (state.pc as isize + sbx as isize) as usize;
                        state.vals[state.base + a as usize + 3] = LBoxed::from_number(idx);
                    }
                },
                Opcode::JMP => {
                    debug!("{:?}", inst.0);
                    let sbx = <JMP as InstructionDecode>::Unpack::unpack(inst.0);
                    debug!("{}", sbx);
                    state.pc = (state.pc as isize + sbx as isize) as usize;
                },
                Opcode::CLOSURE => {
                    let (a, bx) = <CLOSURE as InstructionDecode>::Unpack::unpack(inst.0);
                    let proto = unsafe { &(&(*state.clos.ro(owner).prototype).prototypes.items)[bx as usize] };
                    debug!("{} {} {:?}", a, bx, proto);
                    // handle the MOVE/GETUPVALUE pseudoinstructions
                    let mut fresh = LClosure::new(proto as *const _);
                    {
                        for upval in 0..proto.upval_count {
                            let pseudo = unsafe { (&(*state.clos.ro(owner).prototype).instructions.items)[state.pc+upval as usize] };
                            let label = match pseudo.0.Opcode() {
                                Opcode::MOVE => {
                                    let (_, b) = <MOVE as InstructionDecode>::Unpack::unpack(pseudo.0);
                                    // we can't just copy vals[b], because we need
                                    // to reference the stack slot not the value.
                                    // instead we reference the stack slot, and add
                                    // this new use to the list of uses. on CLOSE
                                    // we will iterate over all these uses and close
                                    // them - but only then.
                                    let fresh_upval = Upvalue::Open(b as usize);
                                    let fresh_use = Tc::new(fresh_upval.clone());
                                    fresh.upvalues.push(fresh_use.clone());
                                    state.upvals.push((fresh_upval, vec![fresh_use].into()));
                                    "move"
                                },
                                Opcode::GETUPVAL => {
                                    let (_, b) = <GETUPVAL as InstructionDecode>::Unpack::unpack(pseudo.0);
                                    // the upvalue already exists in our current
                                    // scope. add ourselves to the existing
                                    // use list.
                                    let fresh_use = Tc::new(state.upvals[b as usize].clone().0);
                                    fresh.upvalues.push(fresh_use.clone());
                                    state.upvals[b as usize].1.push(fresh_use);
                                    "getupvval"
                                },
                                _ => panic!(),
                            };
                            debug!("pseudo: {:?} ({})", pseudo, label);
                        }
                        state.pc += proto.upval_count as usize;
                        //assert_eq!(proto.upval_count, 0);
                    }
                    state.vals[state.base + a as usize] = LBoxed::box_lvalue(LValue::LClosure(Tc::new(fresh)));
                },
                Opcode::CALL => {
                    let (a, b, c) = <CALL as InstructionDecode>::Unpack::unpack(inst.0);
                    debug!("{} {} {}", a, b, c);
                    let to_call = state.vals[state.base + a as usize].unbox();
                    debug!("{:?}", to_call);
                    // push where to return to once we RETURN
                    if let LValue::LClosure(ref lclos) = to_call {
                        let next_stack = state.call_lua(owner, ReturnLocation::Interpreter(state.pc).pack(),
                            a as u16, b as u16, c as u16
                        );
                        #[cfg(feature = "lbbv")]
                        {
                            if LBBV {
                                // TODO: only run LBBV for hot code
                                let types = vec![LType::Unknown; next_stack];
                                let ctx = Rc::new(Context::new(types));
                                let versions = spec.versions.entry(lclos.ro(owner).prototype).or_insert_with(|| HashMap::default());
                                let block = if let Some(block) = versions.get(&(SubPc::new(0), ctx.clone())) {
                                    *block
                                } else {
                                    spec.set_current(lclos.clone());
                                    spec.block(owner, 0, ctx)
                                };
                                debug!("{:?} {block:?}", spec.blocks);
                                spec.set_current(lclos.clone());
                                let (r_state, r_vals) = spec.run(gc, owner, block, state);
                                state = r_state;
                                // Unlike a normal call, LBBV might have returned *out* of our current
                                // function and exitted the top-level.
                                if let Some(r_vals) = r_vals {
                                    break 'int r_vals;
                                }
                            } else {
                                state.pc = 0;
                            }
                        }
                        #[cfg(not(feature = "lbbv"))]
                        {
                            let _ = next_stack;
                            state.pc = 0;
                        }
                    } else if let LValue::NClosure(ncall) = to_call {
                        let nf = ncall.native();
                        // Publish roots so a native (e.g. `collectgarbage`) can reach them.
                        // See Note [GC roots].
                        gc.publish(&state, &spec);
                        state.call_native(nf, a as u16, b, c, owner);
                        // FIXME(metatables): __call
                    } else {
                        panic!("cant call {:?}", to_call);
                    }
                },
                Opcode::RETURN => {
                    let (a, b) = <RETURN as InstructionDecode>::Unpack::unpack(inst.0);
                    debug!("{} {}", a, b);
                    match state.do_return(owner, a as usize, b as usize) {
                        Ok(ReturnLocation::Interpreter(caller)) => {
                            state.pc = caller;
                        },
                        Ok(ReturnLocation::Generator(block, off)) => {
                            unimplemented!()
                        },
                        Err(r_vals) => {
                            break 'int r_vals;
                        },
                    }
                },
                Opcode::INVALID => unreachable!(),
                x => unimplemented!("opcode {:?}", x),
                _ => (),
            };
        };
        #[cfg(all(feature = "counters", feature = "lbbv", not(test)))] {
            println!("counters after run {:?} instructions {:?}", state.counters, spec.count());
        }
        #[cfg(all(feature = "counters", not(feature = "lbbv"), not(test)))] {
            println!("counters after run {:?}", state.counters);
        }

        #[cfg(all(feature = "graph", feature = "lbbv"))]
        for proto in unsafe { &(*self.top_level).prototypes.items } {
            let outfile = format!("func_{}.pdf", proto.line_defined);
            spec.dump(owner, proto, outfile.as_str());
        }

        // Decode the boxed return values back into the `LValue` view for callers.
        Ok(r_vals.into_iter().map(|b| b.unbox()).collect::<Vec<_>>().into())
    }

}
