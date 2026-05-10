#![allow(non_snake_case, unused)]
use core::fmt::Debug;
use core::hash::Hash;
use std::num::Wrapping;
use std::ops::{DerefMut, Index, IndexMut};
use crate::chunk::FunctionBlock;
use crate::chunk::{InstBits, Constant};
use rustc_hash::FxBuildHasher;
use std::borrow::Cow;
use std::cell::{RefCell, Cell};
use std::collections::HashMap;
use std::hash::BuildHasher;
use std::{error::Error, ops::Deref};
use std::io::Write;

use internment::ArenaIntern;
use indexmap::IndexMap;

use qcell::{TCell, TCellOwner};

use log::debug;
use crate::generator::{Specializer, Context, SubPc, BlockId, HashRef};
use crate::perf::PerfCounters;

pub type LConstant<'src, 'intern> = Constant<internment::ArenaIntern<'intern, (&'src [u8], u64)>>;

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
#[derive(Debug, Clone, Copy)]
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
struct FakeRc<T> {
    val: std::ptr::NonNull<T>,
}

impl<T> FakeRc<T> {
    fn new(val: T) -> Self {
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
type Rc<T> = FakeRc<T>;
#[cfg(not(feature = "skip_rc"))]
use std::rc::Rc;

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


#[derive(Debug)]
pub struct Gc<T>(Rc<RefCell<T>>);

impl<T> PartialEq for Gc<T> {
    fn eq(&self, other: &Self) -> bool {
        Rc::as_ptr(&self.0) == Rc::as_ptr(&other.0)
    }
}

impl<T> Eq for Gc<T> { }

impl<T> Hash for Gc<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_usize(Rc::as_ptr(&self.0) as usize)
    }
}

impl<T> Gc<T> {
    fn new(val: T) -> Self {
        Self(Rc::new(RefCell::new(val)))
    }
}

impl<T> Clone for Gc<T> {
    fn clone(&self) -> Self {
        Gc(self.0.clone())
    }
}

impl<T> Deref for Gc<T> {
    type Target = RefCell<T>;

    fn deref(&self) -> &Self::Target {
        self.0.deref()
    }
}

pub struct TcOwner;
pub struct Tc<T>(Rc<TCell<TcOwner, T>>);

impl<T> Debug for Tc<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "tc({:p})", Rc::as_ptr(&self.0))
    }
}

impl<T> PartialEq for Tc<T> {
    fn eq(&self, other: &Self) -> bool {
        Rc::as_ptr(&self.0) == Rc::as_ptr(&other.0)
    }
}

impl<T> Eq for Tc<T> { }

impl<T> Hash for Tc<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        panic!("this doesn't actually work");
        state.write_usize(Rc::as_ptr(&self.0) as usize)
    }
}

impl<T> Tc<T> {
    pub fn new(val: T) -> Self {
        Self(Rc::new(TCell::new(val)))
    }
}

impl<T> Clone for Tc<T> {
    fn clone(&self) -> Self {
        Tc(self.0.clone())
    }
}

impl<T> Deref for Tc<T> {
    type Target = TCell<TcOwner, T>;

    fn deref(&self) -> &Self::Target {
        self.0.deref()
    }
}

#[derive(Default)]
pub struct InternedHasher {
    hasher: FxBuildHasher,
}

pub const fn type_eq<T: ?Sized, U: ?Sized>() -> bool {
    // Helper trait. `VALUE` is false, except for the specialization of the
    // case where `T == U`.
    trait TypeEq<U: ?Sized> {
        const VALUE: bool;
    }

    // Default implementation.
    impl<T: ?Sized, U: ?Sized> TypeEq<U> for T {
        default const VALUE: bool = false;
    }

    // Specialization for `T == U`.
    impl<T: ?Sized> TypeEq<T> for T {
        const VALUE: bool = true;
    }

    <T as TypeEq<U>>::VALUE
}

impl std::hash::BuildHasher for InternedHasher {
    type Hasher = <FxBuildHasher as BuildHasher>::Hasher;

    fn build_hasher(&self) -> Self::Hasher {
        self.hasher.build_hasher()
    }

    fn hash_one<T>(&self, x: T) -> u64
        where T: Hash
    {
        debug!("hashing {:?}", std::any::type_name_of_val(&x));
        if type_eq::<T, &LBoxed>() {
            let lb: &LBoxed = unsafe { std::mem::transmute(&x) };
            if (lb.0 & LBoxed::NUMBER_TAG) == 0 {
                let tag_low = lb.0 & LBoxed::PTR_MASK_LOW;
                let tag_top = lb.0 & LBoxed::PTR_MASK_TOP;
                let ptr = (lb.0 & !LBoxed::PTR_MASK_TOP & !LBoxed::PTR_MASK_LOW) as *const ();
                if tag_top == LBoxed::TAG_TOP_INTERNED && tag_low == LBoxed::TAG_LOW_INTERNED {
                    let ptr = ptr as *const (&[u8], u64);
                    let i = unsafe { &*ptr };
                    debug!("interned hash {:?} {}", i.0, i.1);
                    return i.1;
                }
            }
        }
        self.hasher.hash_one(x)
    }
}

#[derive(Debug)]
pub struct Table {
    pub array: FVec<LBoxed>,
    pub hash: IndexMap<LBoxed, LBoxed, InternedHasher>,
    pub epoch: usize,
}

impl Table {
    pub fn new(array: usize, hash: usize) -> Self {
        Self {
            array: vec![LBoxed::default(); array].into(),
            hash: IndexMap::with_capacity_and_hasher(hash, InternedHasher::default()),
            epoch: 0,
        }
    }
}

impl<'src, 'intern> Tc<Table> {
    pub fn get(&self, owner: &TCellOwner<TcOwner>, key: &LValue<'src, 'intern>) -> Option<LValue<'src, 'intern>> {
        match key {
            LValue::Number(n) => Some(unsafe { self.ro(owner).array.get(n.0 as usize-1).cloned().unwrap_or_default().unbox() }),
            _ => {
                let boxed_key = LBoxed::box_lvalue(key.clone());
                self.ro(owner).hash.get(&boxed_key).map(|v| unsafe { v.unbox() })
            }
        }
    }

    pub fn set(&mut self, owner: &mut TCellOwner<TcOwner>, key: LValue<'src, 'intern>, value: LValue<'src, 'intern>) {
        match key {
            LValue::Number(n) => {
                // TODO: sparse arrays
                if self.rw(owner).array.len() <= n.0 as usize {
                    self.rw(owner).array.resize_with(n.0 as usize, || LBoxed::default());
                }
                self.rw(owner).array[n.0 as usize-1] = LBoxed::box_lvalue(value)
            },
            _ => {
                let boxed_key = LBoxed::box_lvalue(key);
                let boxed_val = LBoxed::box_lvalue(value);
                self.rw(owner).hash.insert(boxed_key, boxed_val);
                self.rw(owner).epoch += 1;
            }
        }
    }
}

#[repr(u8)]
#[derive(Hash, Clone)]
pub enum InternString<'intern, 'src> {
    Interned(ArenaIntern<'intern, (&'src [u8], u64)>),
    Owned(Rc<FVec<u8>>),
}

impl<'intern, 'src> PartialEq for InternString<'intern, 'src> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (InternString::Interned(self_s), InternString::Interned(other_s)) => {
                if self_s.deref().0.as_ptr() == other_s.deref().0.as_ptr() {
                    return true
                } else {
                    return self_s == other_s
                }
            },
            (InternString::Interned(inter), InternString::Owned(own)) |
            (InternString::Owned(own), InternString::Interned(inter)) => {
                inter.deref().0 == own.as_slice()
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
                if self_s.deref().0.as_ptr() == other_s.deref().0.as_ptr() {
                    self_s.partial_cmp(self_s)
                } else {
                    self_s.partial_cmp(other_s)
                }
            },
            (InternString::Interned(inter), InternString::Owned(own)) |
            (InternString::Owned(own), InternString::Interned(inter)) => {
                inter.0.partial_cmp(own.as_slice())
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
            InternString::Interned(i) => write!(f, "{}", String::from_utf8_lossy(i.0)),
            InternString::Owned(o) => write!(f, "{}", String::from_utf8_lossy(o)),
        }
    }
}

impl<'intern, 'src> InternString<'intern, 'src> {
    pub fn intern<S: Into<String>>(intern: &'intern internment::Arena<(&'src [u8], u64)>, s: S) -> LValue<'src, 'intern> {
        // this is stupid: we probably actually need to intern Cow<'src, [u8]>
        let s: String = s.into();
        let static_s: &'static [u8] = Box::leak(s.into_boxed_str().into());
        use std::hash::BuildHasher;
        let hash = FxBuildHasher::default().hash_one(static_s);
        debug!("interning hash {} for {:?}", hash, static_s);
        LValue::InternedString(intern.intern((static_s.as_ref(), hash)))
    }
}

impl<'intern, 'src> Deref for InternString<'intern, 'src> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        match self {
            InternString::Interned(i) => i.deref().0,
            InternString::Owned(o) => o.as_ref(),
        }
    }
}

#[repr(u8)]
#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub enum LValue<'src, 'intern> {
    Nil,
    Bool(bool),
    Number(Number),
    InternedString(ArenaIntern<'intern, (&'src [u8], u64)>),
    OwnedString(Rc<FVec<u8>>),
    LClosure(Tc<LClosure<'src, 'intern>>),
    NClosure(Tc<NClosure>),
    Table(Tc<Table>),
}

#[derive(Debug, Eq, Hash)]
#[repr(transparent)]
pub struct LBoxed(pub u64);

impl LBoxed {
    pub const NUMBER_TAG: u64 = 0xfffe000000000000;
    pub const DOUBLE_ENCODE_OFFSET: u64 = 0x0002000000000000;
    pub const OTHER_TAG: u64 = 0x2;
    pub const BOOL_TAG: u64 = 0x4;
    pub const VALUE_NULL: u64 = Self::OTHER_TAG;
    pub const VALUE_FALSE: u64 = Self::OTHER_TAG | Self::BOOL_TAG | 0;
    pub const VALUE_TRUE: u64 = Self::OTHER_TAG | Self::BOOL_TAG | 1;

    pub const PTR_MASK_TOP: u64 = 0xffff000000000000;
    pub const PTR_MASK_LOW: u64 = 0x7;

    pub const TAG_TOP_TABLE: u64 = 0x0000000000000000;
    pub const TAG_LOW_TABLE: u64 = 0;

    pub const TAG_TOP_LCLOSURE: u64 = 0x0000000000000000;
    pub const TAG_LOW_LCLOSURE: u64 = 1;

    pub const TAG_TOP_NCLOSURE: u64 = 0x0000000000000000;
    pub const TAG_LOW_NCLOSURE: u64 = 4;

    pub const TAG_TOP_INTERNED: u64 = 0x0000000000000000;
    pub const TAG_LOW_INTERNED: u64 = 5;

    pub const TAG_TOP_OWNED: u64 = 0x0001000000000000;
    pub const TAG_LOW_OWNED: u64 = 0;

    #[inline(always)]
    pub fn box_lvalue<'src, 'intern>(val: LValue<'src, 'intern>) -> Self {
        match val {
            LValue::Nil => LBoxed(Self::VALUE_NULL),
            LValue::Bool(b) => LBoxed(if b { Self::VALUE_TRUE } else { Self::VALUE_FALSE }),
            LValue::Number(n) => {
                let bits = n.0.to_bits();
                LBoxed(bits.wrapping_add(Self::DOUBLE_ENCODE_OFFSET))
            }
            LValue::Table(t) => {
                let ptr = Rc::into_raw(t.0) as u64;
                LBoxed(ptr | Self::TAG_TOP_TABLE | Self::TAG_LOW_TABLE)
            }
            LValue::LClosure(c) => {
                let ptr = Rc::into_raw(c.0) as u64;
                LBoxed(ptr | Self::TAG_TOP_LCLOSURE | Self::TAG_LOW_LCLOSURE)
            }
            LValue::NClosure(c) => {
                let ptr = Rc::into_raw(c.0) as u64;
                LBoxed(ptr | Self::TAG_TOP_NCLOSURE | Self::TAG_LOW_NCLOSURE)
            }
            LValue::InternedString(s) => {
                let ptr = s.into_ref() as *const _ as u64;
                LBoxed(ptr | Self::TAG_TOP_INTERNED | Self::TAG_LOW_INTERNED)
            }
            LValue::OwnedString(s) => {
                let ptr = Rc::into_raw(s) as u64;
                LBoxed(ptr | Self::TAG_TOP_OWNED | Self::TAG_LOW_OWNED)
            }
        }
    }

    #[inline(always)]
    pub unsafe fn unbox<'src, 'intern>(&self) -> LValue<'src, 'intern> {
        if (self.0 & Self::NUMBER_TAG) != 0 {
            // Double or Int32
            let bits = self.0.wrapping_sub(Self::DOUBLE_ENCODE_OFFSET);
            return LValue::Number(Number(f64::from_bits(bits)));
        }

        match self.0 {
            Self::VALUE_NULL => LValue::Nil,
            Self::VALUE_FALSE => LValue::Bool(false),
            Self::VALUE_TRUE => LValue::Bool(true),
            _ => {
                let tag_top = self.0 & Self::PTR_MASK_TOP;
                let tag_low = self.0 & Self::PTR_MASK_LOW;
                let ptr = (self.0 & !Self::PTR_MASK_TOP & !Self::PTR_MASK_LOW) as *const ();
                if tag_top == Self::TAG_TOP_OWNED && tag_low == Self::TAG_LOW_OWNED {
                    let rc = unsafe { Rc::from_raw(ptr as *const FVec<u8>) };
                    let val = LValue::OwnedString(rc.clone());
                    std::mem::forget(rc);
                    return val;
                }
                match tag_low {
                    Self::TAG_LOW_TABLE => {
                        let rc = unsafe { Rc::from_raw(ptr as *const TCell<TcOwner, Table>) };
                        let val = LValue::Table(Tc(rc.clone()));
                        std::mem::forget(rc);
                        val
                    }
                    Self::TAG_LOW_LCLOSURE => {
                        let rc = unsafe { Rc::from_raw(ptr as *const TCell<TcOwner, LClosure<'src, 'intern>>) };
                        let val = LValue::LClosure(Tc(rc.clone()));
                        std::mem::forget(rc);
                        val
                    }
                    Self::TAG_LOW_NCLOSURE => {
                        let rc = unsafe { Rc::from_raw(ptr as *const TCell<TcOwner, NClosure>) };
                        let val = LValue::NClosure(Tc(rc.clone()));
                        std::mem::forget(rc);
                        val
                    }
                    Self::TAG_LOW_INTERNED => {
                        let ptr = ptr as *const (&'src [u8], u64);
                        LValue::InternedString(unsafe { std::mem::transmute(ptr) })
                    }
                    _ => panic!("Invalid LBoxed value: 0x{:x}", self.0),
                }
            }
        }
    }
}

impl Clone for LBoxed {
    fn clone(&self) -> Self {
        unsafe {
            let val = self.unbox();
            Self::box_lvalue(val)
        }
    }
}

impl Drop for LBoxed {
    fn drop(&mut self) {
        if (self.0 & Self::NUMBER_TAG) != 0 {
            return;
        }
        match self.0 {
            Self::VALUE_NULL | Self::VALUE_FALSE | Self::VALUE_TRUE => return,
            _ => {
                let tag_top = self.0 & Self::PTR_MASK_TOP;
                let tag_low = self.0 & Self::PTR_MASK_LOW;
                let ptr = (self.0 & !Self::PTR_MASK_TOP & !Self::PTR_MASK_LOW) as *const ();
                unsafe {
                    if tag_top == Self::TAG_TOP_OWNED && tag_low == Self::TAG_LOW_OWNED {
                        drop(Rc::from_raw(ptr as *const FVec<u8>));
                        return;
                    }
                    match tag_low {
                        Self::TAG_LOW_TABLE => {
                            drop(Rc::from_raw(ptr as *const TCell<TcOwner, Table>));
                        }
                        Self::TAG_LOW_LCLOSURE => {
                            drop(Rc::from_raw(ptr as *const TCell<TcOwner, LClosure>));
                        }
                        Self::TAG_LOW_NCLOSURE => {
                            drop(Rc::from_raw(ptr as *const TCell<TcOwner, NClosure>));
                        }
                        _ => {}
                    }
                }
            }
        }
    }
}

impl PartialEq for LBoxed {
    fn eq(&self, other: &Self) -> bool {
        if self.0 == other.0 {
            return true;
        }
        unsafe { self.unbox() == other.unbox() }
    }
}

impl Default for LBoxed {
    fn default() -> Self {
        LBoxed(Self::VALUE_NULL)
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
    pub fn compare(&self, opcode: Opcode, right: Self) -> Result<bool, String> {
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
                        Ok(left_s.0 < right_s.0),
                    (LValue::OwnedString(left_s), LValue::OwnedString(right_s)) =>
                        Ok(left_s < right_s),
                    _ => panic!()
                }
            },
            Opcode::LE => {
                match (self, &right) {
                    (LValue::Bool(left_b), LValue::Bool(right_b)) => Ok(left_b <= right_b),
                    (LValue::Number(left_n), LValue::Number(right_n)) => Ok(left_n <= right_n),
                    (LValue::InternedString(left_s), LValue::InternedString(right_s)) =>
                        Ok(left_s.0 <= right_s.0),
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

    pub fn len(&self, owner: &TCellOwner<TcOwner>) -> Result<LValue<'src, 'intern>, String> {
        // TODO: metamethods
        match self {
            LValue::InternedString(s) => Ok(LValue::Number(Number(s.0.len() as _))),
            LValue::OwnedString(s) => Ok(LValue::Number(Number(s.len() as _))),
            LValue::Table(t) => {
                // TODO: sparse arrays
                Ok(LValue::Number(Number(t.ro(owner).array.len() as _)))
            },
            _ => unimplemented!(),
        }
    }

    pub fn as_bool(&self, owner: &TCellOwner<TcOwner>) -> Result<LValue<'src, 'intern>, String> {
        match self {
            LValue::Bool(b) => Ok(self.clone()),
            LValue::Nil => Ok(LValue::Bool(false)),
            _ => Ok(LValue::Bool(true)),
        }
    }

    pub fn as_string(&self, owner: &TCellOwner<TcOwner>) -> Option<Rc<FVec<u8>>> {
        // TODO: metamethods?
        match self {
            LValue::OwnedString(s) => Some(s.clone().into()),
            LValue::InternedString(s) => Some(Rc::new(s.into_ref().0.to_vec().into())),
            LValue::Number(f) => {
                let mut s: FVec<_> = vec![].into();
                write!(s, "{}", f.0);
                Some(Rc::new(s))
            },
            LValue::Table(tc) => {
                let mut s: FVec<_> = vec![].into();
                write!(s, "{:?}", tc);
                Some(Rc::new(s))
            },
            LValue::Nil => None,
            LValue::LClosure(l) => {
                let mut s: FVec<_> = vec![].into();
                let line = unsafe { (*l.0.ro(owner).prototype).line_defined };
                let src = unsafe { &(*l.0.ro(owner).prototype).source };
                write!(s, "function({:p}, {:?} @ {})", Rc::as_ptr(&l.0), src, line);
                Some(Rc::new(s))
            },
            x => unimplemented!("{:?}", x),
        }
    }

    pub fn as_string_nolock(&self) -> Option<Rc<FVec<u8>>> {
        // TODO: metamethods?
        match self {
            LValue::OwnedString(s) => Some(s.clone().into()),
            LValue::InternedString(s) => Some(Rc::new(s.into_ref().0.to_vec().into())),
            LValue::Number(f) => {
                let mut s: FVec<_> = vec![].into();
                write!(s, "{}", f.0);
                Some(Rc::new(s))
            },
            LValue::Table(tc) => {
                let mut s: FVec<_> = vec![].into();
                write!(s, "{:?}", tc);
                Some(Rc::new(s))
            },
            LValue::Nil => None,
            LValue::LClosure(l) => {
                let mut s: FVec<_> = vec![].into();
                write!(s, "function({:p})", Rc::as_ptr(&l.0));
                Some(Rc::new(s))
            },
            x => unimplemented!("{:?}", x),
        }
    }

    pub fn gettable(&self, owner: &mut TCellOwner<TcOwner>, index: Cow<'_, LValue<'src, 'intern>>) -> LValue<'src, 'intern> {
        let val_b = match self {
            LValue::Table(tab) => {
                debug!("table {:?}", tab);
                tab.get(owner, index.deref()).ok_or_else(|| Err::<LValue, String>(format!("{:?}", index))).unwrap()
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
pub enum Upvalue {
    Open(usize), // stack index
    Closed(Gc<LBoxed>),
}

pub struct LClosure<'src, 'intern> {
    pub prototype: *const FunctionBlock<'src, LConstant<'src, 'intern>>,
    //environment: LTable<'src>,
    pub upvalues: FVec<Gc<Upvalue>>,
}

impl<'src, 'intern> Debug for LClosure<'src, 'intern> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "closure(upvalues={:?})", self.upvalues)
    }
}

pub trait NativeFunc = for<'a, 'src, 'intern> Fn(&'a [LValue<'src, 'intern>], &mut TCellOwner<TcOwner>) -> FVec<LValue<'src, 'intern>>;
pub struct NClosure {
    pub native: Rc<dyn NativeFunc>,
}

impl<'src> Debug for NClosure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<native function {:p}>", self.native.as_ref())
    }
}

impl<'src, 'intern> LClosure<'src, 'intern> {
    pub fn new(prototype: *const FunctionBlock<'src, LConstant<'src, 'intern>>) -> Self {
        Self {
            prototype,
            upvalues: vec![].into(),
        }
    }
}

#[repr(u8)]
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Closure<'src, 'intern> {
    Lua(Gc<LClosure<'src, 'intern>>),
    Native(Gc<NClosure>),
}

impl NClosure {
    pub fn new(native: impl NativeFunc + 'static) -> Tc<Self> {
        Tc::new(NClosure { native: Rc::new(native) })
    }
}

pub struct Vm<'src, 'intern> {
    // This is terrible, but because we reference FunctionBlocks in Gc<T> types,
    // we can't use proper lifetimes for it: Rust doesn't know that a Gc<T> won't
    // stick around past 'src
    pub top_level: *const FunctionBlock<'src, LConstant<'src, 'intern>>,
}

#[derive(Debug)]
pub enum ReturnLocation {
    Interpreter(usize),
    Generator(BlockId, usize),
}

#[derive(Debug)]
#[repr(C)]
pub struct CallstackEntry<'src, 'intern> { pub clos: Tc<LClosure<'src, 'intern>>, pub ret: ReturnLocation, pub frame: usize, pub limit: usize, pub witness_frame: usize, pub witness_limit: usize, pub rloc: usize, pub c: u16 }

#[repr(C)]
#[derive(Debug)]
pub struct HashWitness {
    pub href: HashRef,
    pub key: LConstant<'static, 'static>,
    pub index: usize,
    pub epoch: usize,
}

#[repr(C)]
#[derive(Debug)]
pub struct RunState<'src, 'intern> {
    pub base: usize,
    pub vals: FVec<LBoxed>,
    pub pc: usize,
    pub _G: Tc<Table>,
    pub clos: Tc<LClosure<'src, 'intern>>,
    pub upvals: FVec<(Upvalue, FVec<Gc<Upvalue>>)>,
    pub callstack: FVec<CallstackEntry<'src, 'intern>>,
    pub counters: PerfCounters,
    pub select: usize,
    pub witness_base: usize,
    pub hash_witnesses: FVec<Option<HashWitness>>,
    pub trap: bool,
    pub current_off: u16,
    pub gas: i64,
}

impl<'src, 'intern> RunState<'src, 'intern> {
    pub fn close_upvalues(&mut self)
    {
        for upval in self.upvals.iter() {
            let idx = match &upval.0 {
                Upvalue::Open(o) => o,
                Upvalue::Closed(u) => panic!(), // we shouldn't have any closed upvals
            };
            // migrate all the stack references to be GC references, since we're
            // going to be removing it from the stack
            let closed = Gc::new(self.vals[*idx].clone());
            for up_use in upval.1.iter() {
                up_use.deref().replace(Upvalue::Closed(closed.clone()));
            }
        }
    }
}


impl<'src, 'intern> Vm<'src, 'intern> {
    pub fn new(top_level: *const FunctionBlock<'src, LConstant<'src, 'intern>>) -> Self {
        Self { top_level }
    }

    pub fn global_env(&self, owner: &mut TCellOwner<TcOwner>, intern: &'intern internment::Arena<(&'src [u8], u64)>) -> Tc<Table> {
        let mut math_tab = Table::new(0, 0);
        math_tab.hash.insert(LBoxed::box_lvalue(InternString::intern(intern, "floor ")), LBoxed::box_lvalue(LValue::NClosure(NClosure::new(|f, _| {
            let f = match f {
                [LValue::Number(f)] => LValue::Number(Number(f.0.floor())),
                _ => unimplemented!()
            };
            return [f].to_vec().into()
        }))));
        math_tab.hash.insert(LBoxed::box_lvalue(InternString::intern(intern, "sqrt ")), LBoxed::box_lvalue(LValue::NClosure(NClosure::new(|f, _| {
            let f = match f {
                [LValue::Number(f)] => LValue::Number(Number(f.0.sqrt())),
                _ => unimplemented!()
            };
            return [f].to_vec().into()
        }))));
        math_tab.hash.insert(LBoxed::box_lvalue(InternString::intern(intern, "abs ")), LBoxed::box_lvalue(LValue::NClosure(NClosure::new(|f, _| {
            let f = match f {
                [LValue::Number(f)] => LValue::Number(Number(f.0.abs())),
                _ => unimplemented!()
            };
            return [f].to_vec().into()
        }))));
        math_tab.hash.insert(LBoxed::box_lvalue(InternString::intern(intern, "huge ")), LBoxed::box_lvalue(LValue::NClosure(NClosure::new(|f, _| {
            return [LValue::Number(Number(f64::INFINITY))].to_vec().into()
        }))));
        math_tab.hash.insert(LBoxed::box_lvalue(InternString::intern(intern, "pi ")), LBoxed::box_lvalue(LValue::Number(Number(std::f64::consts::PI))));
        math_tab.hash.insert(LBoxed::box_lvalue(InternString::intern(intern, "sin ")), LBoxed::box_lvalue(LValue::NClosure(NClosure::new(|f, _| {
            let f = match f {
                [LValue::Number(f)] => LValue::Number(Number(f.0.sin())),
                _ => unimplemented!()
            };
            return [f].to_vec().into()
        }))));
        math_tab.hash.insert(LBoxed::box_lvalue(InternString::intern(intern, "cos ")), LBoxed::box_lvalue(LValue::NClosure(NClosure::new(|f, _| {
            let f = match f {
                [LValue::Number(f)] => LValue::Number(Number(f.0.cos())),
                _ => unimplemented!()
            };
            return [f].to_vec().into()
        }))));
        math_tab.hash.insert(LBoxed::box_lvalue(InternString::intern(intern, "tan ")), LBoxed::box_lvalue(LValue::NClosure(NClosure::new(|f, _| {
            let f = match f {
                [LValue::Number(f)] => LValue::Number(Number(f.0.tan())),
                _ => unimplemented!()
            };
            return [f].to_vec().into()
        }))));

        let mut os_tab = Table::new(0, 0);
        os_tab.hash.insert(LBoxed::box_lvalue(InternString::intern(intern, "exit ")), LBoxed::box_lvalue(LValue::NClosure(NClosure::new(|f, _| {
            let f = match f {
                [LValue::Number(f)] => return std::process::exit(f.0 as i32),
                _ => unimplemented!(),
            };
        }))));

        let math = (LBoxed::box_lvalue(InternString::intern(intern, "math ")), LBoxed::box_lvalue(LValue::Table(Tc::new(math_tab))));
        let os = (LBoxed::box_lvalue(InternString::intern(intern, "os ")), LBoxed::box_lvalue(LValue::Table(Tc::new(os_tab))));
        Tc::new(Table {
            array: vec![].into(),
            hash: IndexMap::<_, _, InternedHasher>::from_iter(
                vec![
                (LBoxed::box_lvalue(InternString::intern(intern, "print ")), LBoxed::box_lvalue(LValue::NClosure(NClosure::new(|v, owner| {
                    let s = v.iter().map(|val| val.as_string(owner)).flat_map(|maybe_str|
                        maybe_str.map(|s| -> String { String::from(String::from_utf8_lossy(s.as_slice()).to_owned()) })
                    ).collect::<Vec<_>>();
                    println!("> {}", s.iter().intersperse(&" ".to_string()).cloned().collect::<String>());
                    vec![LValue::Nil].into()
                })))),
                (LBoxed::box_lvalue(InternString::intern(intern, "assert ")), LBoxed::box_lvalue(LValue::NClosure(NClosure::new(|v, owner| {
                    match v {
                        [LValue::Bool(b), ..] => {
                            if !b {
                                panic!("lua assert failed");
                            }
                        },
                        _ => { },
                    };
                    vec![].into()
                })))),
                math,
                os,
                ].drain(..)
            ),
            epoch: 0,
        })
    }

    pub fn rk<'exec>(proto: *const FunctionBlock<'src, LConstant<'src, 'intern>>, base: usize, vals: &'exec FVec<LBoxed>, r: u16)
        -> Result<&'exec LConstant<'src, 'intern>, &'exec LBoxed>
    {
        if (r & 0x100)!=0 {
            let r_const = r & (0xff);
            debug!("rk {}", r_const);
            Ok(unsafe { &(&(*proto).constants.items)[r_const as usize] })
        } else {
            Err(&vals[base + r as usize])
        }
    }

    pub fn run<'lua, const LBBV: bool>(&'lua self,
        owner: &mut TCellOwner<TcOwner>,
        mut _G: Tc<Table>,
        mut clos: Tc<LClosure<'src, 'intern>>,
        mut args: FVec<LValue<'src, 'intern>>,
    )
        -> Result<FVec<LValue<'src, 'intern>>, Box<dyn Error>>
        where 'src: 'lua
    {
        let mut boxed_args: FVec<LBoxed> = args.into_iter().map(LBoxed::box_lvalue).collect::<Vec<_>>().into();
        boxed_args.resize_with(unsafe {
            (*clos.ro(owner).prototype).max_stack as usize
        }, || LBoxed::default());

        let mut spec = Specializer::new(clos.clone());
        let mut state = {
            let mut vals = boxed_args;
            let mut upvals: FVec<(Upvalue, FVec<Gc<Upvalue>>)> = vec![].into();
            let mut base = 0;
            let mut witness_base = 0;
            let mut pc = 0;
            let mut callstack: FVec<_> = vec![].into();

            RunState {
                base,
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
            }
        };
        let r_vals = 'int: loop {
            let inst = unsafe { state.clos.ro(owner).prototype.as_ref().unwrap().instructions.items[state.pc] };
            state.pc += 1;
            state.counters.interpreter_count.increment();
            debug!("pc {} inst {:?}", state.pc, inst.0.Opcode());
            match inst.0.Opcode() {
                Opcode::MOVE => {
                    let (a, b) = <MOVE as InstructionDecode>::Unpack::unpack(inst.0);
                    state.vals[state.base + a as usize] = state.vals[state.base + b as usize].clone();
                },
                Opcode::GETUPVAL => {
                    let (a, b) = <GETUPVAL as InstructionDecode>::Unpack::unpack(inst.0);
                    let upval = match state.clos.ro(owner).upvalues[b as usize].borrow().deref() {
                        Upvalue::Open(o) => {
                            state.vals[*o as usize].clone()
                        },
                        Upvalue::Closed(c) => {
                            c.borrow().clone()
                        },
                    };
                    state.vals[state.base + a as usize] = upval;
                },
                Opcode::SETUPVAL => {
                    let (a, b) = <SETUPVAL as InstructionDecode>::Unpack::unpack(inst.0);
                    match state.clos.ro(owner).upvalues[b as usize].borrow().deref() {
                        Upvalue::Open(o) => {
                            state.vals[*o as usize] = state.vals[state.base + a as usize].clone()
                        },
                        Upvalue::Closed(c) => {
                            let val = unsafe { state.vals[state.base + a as usize].unbox() }; *c.borrow_mut() = LBoxed::box_lvalue(val)
                        },
                    };
                },
                Opcode::LOADK => {
                    let (a, bx) = <LOADK as InstructionDecode>::Unpack::unpack(inst.0);
                    state.vals[state.base + a as usize] = LBoxed::box_lvalue(unsafe { (&(&(*state.clos.ro(owner).prototype).constants.items)[bx as usize]).into() });
                },
                Opcode::LOADNIL => {
                    let (a, b) = <LOADNIL as InstructionDecode>::Unpack::unpack(inst.0);
                    state.vals[state.base + a as usize..=state.base + b as usize].iter_mut().for_each(|i| *i = LBoxed::default());
                },
                Opcode::LOADBOOL => {
                    let (a, b, c) = <LOADBOOL as InstructionDecode>::Unpack::unpack(inst.0);
                    state.vals[state.base + a as usize] = LBoxed::box_lvalue(LValue::Bool(b != 0));
                    if c != 0 {
                        state.pc += 1;
                    }
                },
                Opcode::NEWTABLE => {
                    let (a, b, c) = <NEWTABLE as InstructionDecode>::Unpack::unpack(inst.0);
                    state.vals[state.base + a as usize] = LBoxed::box_lvalue(LValue::Table(Tc::new(Table::new(b as usize, c as usize))));
                },
                Opcode::SELF => {
                    let (a, b, c) = <SELF as InstructionDecode>::Unpack::unpack(inst.0);
                    let rb = state.vals[state.base + b as usize].clone();
                    state.vals[state.base + a as usize + 1] = rb.clone();
                    let kc = match Self::rk(state.clos.ro(owner).prototype, state.base, &state.vals, c) {
                        Ok(c) => Cow::Owned(LValue::from(c)),
                        Err(lv) => Cow::Owned(unsafe { lv.unbox() }),
                    };
                    let res = unsafe { rb.unbox() }.gettable(owner, kc);
                    state.vals[state.base + a as usize] = LBoxed::box_lvalue(res);
                },
                Opcode::SETLIST => {
                    let (a, b, c) = <SETLIST as InstructionDecode>::Unpack::unpack(inst.0);
                    let val_a = unsafe { state.vals[state.base + a as usize].unbox() };
                    match val_a {
                        LValue::Table(tab) => {
                            assert_ne!(c, 0);
                            if b == 0 {
                                let src = state.vals[state.base + a as usize + 1..].iter().cloned();
                                tab.rw(owner).array.splice((c as usize - 1) * 50.., src).for_each(drop);
                            } else {
                                let src = state.vals[state.base + a as usize + 1..=state.base + a as usize + b as usize].iter().cloned();
                                tab.rw(owner).array.splice((c as usize - 1) * 50.., src).for_each(drop);
                            }
                        },
                        _ => unimplemented!(),
                    }
                },
                Opcode::GETTABLE => {
                    let (a, b, c) = <GETTABLE as InstructionDecode>::Unpack::unpack(inst.0);
                    let kc = match Self::rk(state.clos.ro(owner).prototype, state.base, &state.vals, c) {
                        Ok(c) => Cow::Owned(LValue::from(c)),
                        Err(lv) => Cow::Owned(unsafe { lv.unbox() }),
                    };
                    let val_b = unsafe { state.vals[state.base + b as usize].unbox() };
                    state.vals[state.base + a as usize] = LBoxed::box_lvalue(val_b.gettable(owner, kc));
                },
                Opcode::SETTABLE => {
                    let (a, b, c) = <SETTABLE as InstructionDecode>::Unpack::unpack(inst.0);
                    let kb = match Self::rk(state.clos.ro(owner).prototype, state.base, &state.vals, b) {
                        Ok(b) => b.into(),
                        Err(lv) => unsafe { lv.unbox() },
                    };
                    let kc = match Self::rk(state.clos.ro(owner).prototype, state.base, &state.vals, c) {
                        Ok(c) => c.into(),
                        Err(lv) => unsafe { lv.unbox() },
                    };
                    match unsafe { state.vals[state.base + a as usize].unbox() } {
                        LValue::Table(mut tab) => {
                            tab.set(owner, kb, kc)
                        },
                        x => unimplemented!(),
                    };
                },
                Opcode::SETGLOBAL => {
                    let (a, bx) = <SETGLOBAL as InstructionDecode>::Unpack::unpack(inst.0);
                    let kst = unsafe { &(&(*state.clos.ro(owner).prototype).constants.items)[bx as usize] };
                    state._G.set(owner, kst.into(), unsafe { state.vals[state.base + a as usize].unbox() });
                },
                Opcode::GETGLOBAL => {
                    let (a, bx) = <GETGLOBAL as InstructionDecode>::Unpack::unpack(inst.0);
                    let kst = unsafe { &(&(*state.clos.ro(owner).prototype).constants.items)[bx as usize] };
                    state.vals[state.base + a as usize] = LBoxed::box_lvalue(state._G.get(owner, &kst.into()).unwrap_or(LValue::Nil));
                },
                Opcode::TEST => {
                    let (a, _, c) = <TEST as InstructionDecode>::Unpack::unpack(inst.0);
                    if let LValue::Bool(b) = (unsafe { state.vals[state.base + a as usize].unbox() }.as_bool(owner)?) && (b as u16) == c {
                    } else {
                        state.pc += 1;
                    }
                },
                opcode @ (Opcode::EQ | Opcode::LT | Opcode::LE) => {
                    let (a, b, c) = ABC::unpack(inst.0);
                    let kb = Self::rk(state.clos.ro(owner).prototype, state.base, &state.vals, b);
                    let kc = Self::rk(state.clos.ro(owner).prototype, state.base, &state.vals, c);
                    let cond = match (opcode, kb, kc) {
                        (Opcode::EQ, Ok(cb), Ok(cc)) => cb == cc,
                        (Opcode::LT, Ok(cb), Ok(cc)) => cb < cc,
                        (Opcode::LE, Ok(cb), Ok(cc)) => cb <= cc,
                        (_, Err(db), Ok(cc)) => unsafe { db.unbox() }.compare(opcode, cc.into()).unwrap(),
                        (_, Ok(cb), Err(dc)) => LValue::from(cb).compare(opcode, unsafe { dc.unbox() }).unwrap(),
                        (_, Err(db), Err(dc)) => unsafe { db.unbox() }.compare(opcode, unsafe { dc.unbox() }).unwrap(),
                        _ => panic!(),
                    };
                    if (cond as u8) != a {
                        state.pc += 1;
                    }
                },
                opcode @ (Opcode::ADD | Opcode::SUB | Opcode::MUL | Opcode::DIV | Opcode::MOD | Opcode::POW) => {
                    let (a, b, c) = ABC::unpack(inst.0);
                    let kb = Self::rk(state.clos.ro(owner).prototype, state.base, &state.vals, b);
                    let kc = Self::rk(state.clos.ro(owner).prototype, state.base, &state.vals, c);
                    let res = match (opcode, kb, kc) {
                        (Opcode::ADD, Ok(Constant::Number(cb)), Ok(Constant::Number(cc))) => LValue::Number(Number(cb.0 + cc.0)),
                        (Opcode::SUB, Ok(Constant::Number(cb)), Ok(Constant::Number(cc))) => LValue::Number(Number(cb.0 - cc.0)),
                        (Opcode::MUL, Ok(Constant::Number(cb)), Ok(Constant::Number(cc))) => LValue::Number(Number(cb.0 * cc.0)),
                        (Opcode::DIV, Ok(Constant::Number(cb)), Ok(Constant::Number(cc))) => LValue::Number(Number(cb.0 / cc.0)),
                        (Opcode::MOD, Ok(Constant::Number(cb)), Ok(Constant::Number(cc))) => LValue::Number(Number(cb.0 % cc.0)),
                        (Opcode::POW, Ok(Constant::Number(cb)), Ok(Constant::Number(cc))) => LValue::Number(Number(cb.0.powf(cc.0))),
                        (_, Ok(cb), Err(dc)) => LValue::from(cb).numeric_op(opcode, &unsafe { dc.unbox() })?,
                        (_, Err(db), Ok(cc)) => unsafe { db.unbox() }.numeric_op(opcode, &cc.into())?,
                        (_, Err(db), Err(dc)) => unsafe { db.unbox() }.numeric_op(opcode, &unsafe { dc.unbox() })?,
                        _ => unimplemented!(),
                    };
                    state.vals[state.base + a as usize] = LBoxed::box_lvalue(res);
                },
                Opcode::UNM => {
                    let (a, b) = <UNM as InstructionDecode>::Unpack::unpack(inst.0);
                    let b_val = unsafe { state.vals[state.base + b as usize].unbox() };
                    let res = match b_val {
                        LValue::Number(n) => LValue::Number(Number(-n.0)),
                        _ => unimplemented!(),
                    };
                    state.vals[state.base + a as usize] = LBoxed::box_lvalue(res);
                },
                Opcode::LEN => {
                    let (a, b) = <LEN as InstructionDecode>::Unpack::unpack(inst.0);
                    let b_val = unsafe { state.vals[state.base + b as usize].unbox() };
                    state.vals[state.base + a as usize] = LBoxed::box_lvalue(b_val.len(owner)?);
                },
                Opcode::CONCAT => {
                    let (a, b, c) = <CONCAT as InstructionDecode>::Unpack::unpack(inst.0);
                    let mut s: FVec<_> = vec![].into();
                    for i in (b as usize)..=(c as usize) {
                        let i_val = unsafe { state.vals[state.base + i as usize].unbox() };
                        s.extend_from_slice(&i_val.as_string(owner).ok_or("nil concat")?);
                    }
                    state.vals[state.base + a as usize] = LBoxed::box_lvalue(LValue::OwnedString(Rc::new(s)));
                },
                Opcode::FORPREP => {
                    let (a, sbx) = <FORPREP as InstructionDecode>::Unpack::unpack(inst.0);
                    let a_val = unsafe { state.vals[state.base + a as usize].unbox() };
                    let step_val = unsafe { state.vals[state.base + a as usize + 2].unbox() };
                    state.vals[state.base + a as usize] = LBoxed::box_lvalue(a_val.numeric_op(Opcode::SUB, &step_val).unwrap());
                    state.pc = (state.pc as isize + sbx as isize) as usize;
                },
                Opcode::FORLOOP => {
                    let (a, sbx) = <FORLOOP as InstructionDecode>::Unpack::unpack(inst.0);
                    let step = unsafe { state.vals[state.base + a as usize + 2].unbox() };
                    let a_val = unsafe { state.vals[state.base + a as usize].unbox() };
                    let idx = a_val.numeric_op(Opcode::ADD, &step).unwrap();
                    state.vals[state.base + a as usize] = LBoxed::box_lvalue(idx.clone());
                    let limit = unsafe { state.vals[state.base + a as usize + 1].unbox() };
                    let comp = if step.compare(Opcode::LT, LValue::from(&Constant::Number(Number(0.0))))? {
                        limit.compare(Opcode::LE, idx.clone())
                    } else {
                        idx.clone().compare(Opcode::LE, limit)
                    };
                    if comp? {
                        state.pc = (state.pc as isize + sbx as isize) as usize;
                        state.vals[state.base + a as usize + 3] = LBoxed::box_lvalue(idx);
                    }
                },
                Opcode::JMP => {
                    let sbx = <JMP as InstructionDecode>::Unpack::unpack(inst.0);
                    state.pc = (state.pc as isize + sbx as isize) as usize;
                },
                Opcode::CLOSURE => {
                    let (a, bx) = <CLOSURE as InstructionDecode>::Unpack::unpack(inst.0);
                    let proto = unsafe { &(&(*state.clos.ro(owner).prototype).prototypes.items)[bx as usize] };
                    let mut fresh = LClosure::new(proto as *const _);
                    for upval_idx in 0..proto.upval_count {
                        let pseudo = unsafe { (&(*state.clos.ro(owner).prototype).instructions.items)[state.pc + upval_idx as usize] };
                        match pseudo.0.Opcode() {
                            Opcode::MOVE => {
                                let (_, b) = <MOVE as InstructionDecode>::Unpack::unpack(pseudo.0);
                                let fresh_upval = Upvalue::Open(b as usize);
                                let fresh_use = Gc::new(fresh_upval.clone());
                                fresh.upvalues.push(fresh_use.clone());
                                state.upvals.push((fresh_upval, vec![fresh_use].into()));
                            },
                            Opcode::GETUPVAL => {
                                let (_, b) = <GETUPVAL as InstructionDecode>::Unpack::unpack(pseudo.0);
                                let fresh_use = Gc::new(state.upvals[b as usize].0.clone());
                                fresh.upvalues.push(fresh_use.clone());
                                state.upvals[b as usize].1.push(fresh_use);
                            },
                            _ => panic!(),
                        }
                    }
                    state.pc += proto.upval_count as usize;
                    state.vals[state.base + a as usize] = LBoxed::box_lvalue(LValue::LClosure(Tc::new(fresh)));
                },
                Opcode::CALL => {
                    let (a, b, c) = <CALL as InstructionDecode>::Unpack::unpack(inst.0);
                    let to_call_boxed = &state.vals[state.base + a as usize];
                    let to_call = unsafe { to_call_boxed.unbox() };
                    if let LValue::LClosure(ref lclos) = to_call {
                        let next_stack = unsafe { (*lclos.ro(owner).prototype).max_stack as usize };
                        state.vals.extend_from_slice(vec![LBoxed::default(); next_stack].as_slice());
                        state.callstack.push(CallstackEntry {
                            clos: state.clos.clone(),
                            ret: ReturnLocation::Interpreter(state.pc),
                            frame: state.base,
                            limit: state.vals.len(),
                            rloc: state.base + a as usize,
                            witness_frame: state.witness_base,
                            witness_limit: state.hash_witnesses.len(),
                            c
                        });
                        state.base = state.base + a as usize + 1;
                        state.witness_base = state.hash_witnesses.len();
                        state.vals.truncate(state.base + next_stack);
                        state.clos = lclos.clone();
                        if LBBV {
                            let types = vec![LType::Unknown; next_stack];
                            let ctx = Context::new(types);
                            let versions = spec.versions.entry(lclos.ro(owner).prototype).or_insert_with(|| HashMap::default());
                            let block = if let Some(block) = versions.get(&(SubPc::new(0), ctx.clone())) {
                                *block
                            } else {
                                spec.set_current(lclos.clone());
                                spec.block(owner, 0, ctx)
                            };
                            spec.set_current(lclos.clone());
                            state = spec.run(owner, block, state);
                        } else {
                            state.pc = 0;
                        }
                    } else if let LValue::NClosure(ncall) = to_call {
                        let args_boxed = if b == 0 {
                            &state.vals[state.base + a as usize + 1..]
                        } else {
                            &state.vals[state.base + a as usize + 1..=(state.base + a as usize + b as usize - 1)]
                        };
                        let args: Vec<LValue> = args_boxed.iter().map(|v| unsafe { v.unbox() }).collect();
                        let mut native = ncall.rw(owner).native.clone();
                        let ret = (native)(&args, owner);
                        let boxed_ret = ret.into_iter().map(LBoxed::box_lvalue);
                        if c == 0 {
                            state.vals.splice(state.base + a as usize.., boxed_ret).for_each(drop);
                        } else if c != 1 {
                            state.vals.splice(state.base + a as usize..state.base + a as usize + c as usize - 2, boxed_ret).for_each(drop);
                        }
                    } else {
                        panic!("cant call {:?}", to_call);
                    }
                },
                Opcode::RETURN => {
                    state.close_upvalues();
                    state.upvals = vec![].into();
                    let (a, b) = <RETURN as InstructionDecode>::Unpack::unpack(inst.0);
                    let r_count: usize;
                    let r_vals: FVec<LBoxed> = if b == 1 {
                        r_count = 0;
                        vec![].into()
                    } else if b >= 2 {
                        r_count = b as usize - 1;
                        state.vals[state.base + a as usize..(state.base + a as usize + r_count)].to_vec().into()
                    } else {
                        let r_v = &state.vals[state.base + a as usize..];
                        r_count = r_v.len();
                        r_v.to_vec().into()
                    };
                    match state.callstack.pop() {
                        Some(CallstackEntry { clos: ret_clos, ret: ReturnLocation::Interpreter(caller), frame, witness_frame, limit, witness_limit, rloc, c }) => {
                            state.clos = ret_clos;
                            state.base = frame;
                            state.witness_base = witness_frame;
                            if c == 1 {
                                state.vals.truncate(limit);
                            } else if c >= 2 {
                                for i in 0..=(c - 2) {
                                    state.vals[rloc + i as usize] = r_vals[i as usize].clone();
                                }
                                state.vals.truncate(limit);
                            } else {
                                for (i, v) in r_vals.into_iter().enumerate() {
                                    state.vals[rloc + i] = v;
                                }
                                state.vals.truncate(rloc + r_count);
                            }
                            state.hash_witnesses.truncate(witness_limit);
                            state.pc = caller;
                        },
                        None => {
                            let unboxed_r: FVec<LValue> = r_vals.into_iter().map(|v| unsafe { v.unbox() }).collect::<Vec<_>>().into();
                            break 'int unboxed_r;
                        },
                        _ => unimplemented!(),
                    }
                },
                Opcode::INVALID => unreachable!(),
                _ => {},
            }
        };
        #[cfg(feature = "counters")] { println!("counters after run {:?}", state.counters); }
        #[cfg(feature = "graph")]
        for proto in unsafe { &(*self.top_level).prototypes.items } {
            let outfile = format!("func_{}.pdf", proto.line_defined);
            spec.dump(owner, proto, outfile.as_str());
        }
        Ok(r_vals)
    }

}

impl<'src, 'intern> From<&LConstant<'src, 'intern>> for LBoxed {
    fn from(value: &LConstant<'src, 'intern>) -> Self {
        LBoxed::box_lvalue(LValue::from(value))
    }
}
