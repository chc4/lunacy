#![allow(non_snake_case)]
use core::fmt::Debug;
use core::hash::Hash;
use std::ops::{DerefMut, Index, IndexMut};
use crate::chunk::FunctionBlock;
use crate::chunk::{InstBits, Constant};
use rustc_hash::FxBuildHasher;
use std::borrow::Cow;
use std::cell::{RefCell, Cell};
use std::collections::HashMap;
use std::hash::BuildHasher;
use std::{error::Error, ops::Deref};

use internment::ArenaIntern;

use qcell::{TCell, TCellOwner};

use log::debug;

type LConstant<'src, 'intern> = Constant<internment::ArenaIntern<'intern, (&'src [u8], u64)>>;

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

trait Instruction {
    type Unpack: Unpacker;
}

trait Unpacker {
    type Unpacked;
    #[inline(always)]
    fn unpack(inst: InstBits) -> Self::Unpacked;
}

struct AB;
impl Unpacker for AB {
    type Unpacked = (u8, u16); // A: 8, B: 9
    fn unpack(inst: InstBits) -> Self::Unpacked {
        (inst.A() as u8, inst.B() as u16)
    }
}

struct ABx;
impl Unpacker for ABx {
    type Unpacked = (u8, u32); // A: 8, Bx: 18
    fn unpack(inst: InstBits) -> Self::Unpacked {
        (inst.A() as u8, inst.Bx() as u32)
    }
}

struct ABC;
impl Unpacker for ABC {
    type Unpacked = (u8, u16, u16); // A: 8, B: 9, C: 9
    fn unpack(inst: InstBits) -> Self::Unpacked {
        (inst.A() as u8, inst.B() as u16, inst.C() as u16)
    }
}

struct sBx;
impl Unpacker for sBx {
    type Unpacked = i32; // A: 8, B: 9, C: 9
    fn unpack(inst: InstBits) -> Self::Unpacked {
        // 131071 = 2^18-1 >> 1, aka half the bias
        (inst.Bx() - 131071) as i32
    }
}

struct AsBx;
impl Unpacker for AsBx {
    type Unpacked = (u8, i32); // A: 8, sBx: 18
    fn unpack(inst: InstBits) -> Self::Unpacked {
        // 131071 = 2^18-1 >> 1, aka half the bias
        (inst.A() as u8, (inst.Bx() as isize - 131071) as i32)
    }
}


struct MOVE;
impl Instruction for MOVE { type Unpack = AB; }

struct GETUPVAL;
impl Instruction for GETUPVAL{ type Unpack = AB; }

struct LOADK;
impl Instruction for LOADK { type Unpack = ABx; }

struct RETURN;
impl Instruction for RETURN { type Unpack = AB; }

struct CLOSURE;
impl Instruction for CLOSURE { type Unpack = ABx; }

struct SETGLOBAL;
impl Instruction for SETGLOBAL { type Unpack = ABx; }

struct CALL;
impl Instruction for CALL { type Unpack = ABC; }

struct EQ;
impl Instruction for EQ { type Unpack = ABC; }

struct JMP;
impl Instruction for JMP { type Unpack = sBx; }

struct NEWTABLE;
impl Instruction for NEWTABLE { type Unpack = ABC; }

struct GETTABLE;
impl Instruction for GETTABLE { type Unpack = ABC; }

struct SETTABLE;
impl Instruction for SETTABLE { type Unpack = ABC; }

struct SETLIST;
impl Instruction for SETLIST { type Unpack = ABC; }

struct FORPREP;
impl Instruction for FORPREP { type Unpack = AsBx; }

struct FORLOOP;
impl Instruction for FORLOOP { type Unpack = AsBx; }

struct LEN;
impl Instruction for LEN { type Unpack = AB; }

struct UNM;
impl Instruction for UNM { type Unpack = AB; }


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
type FVec<T> = UnsafeVec<T>;
#[cfg(not(feature = "skip_vec"))]
type FVec<T> = Vec<T>;


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
struct InternedHasher {
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
        if type_eq::<T, &LValue<'_, '_>>() {
            let lv: &&LValue<'_, '_> = unsafe { std::mem::transmute(&x) };
            match lv {
                LValue::InternedString(i) => {
                    debug!("interned hash {:?} {}", i.0, i.1);
                    //assert_eq!(self.hasher.hash_one(i.0), i.1);
                    return i.1
                },
                _ => (),
            }
        }
        self.hasher.hash_one(x)
    }
}

#[derive(Debug)]
pub struct Table<'src, 'intern> {
    array: FVec<LValue<'src, 'intern>>,
    hash: HashMap<LValue<'src, 'intern>, LValue<'src, 'intern>, InternedHasher>,
}

impl<'src, 'intern> Table<'src, 'intern> {
    pub fn new(array: usize, hash: usize) -> Self {
        Self {
            array: vec![LValue::Nil; array].into(),
            hash: HashMap::with_capacity_and_hasher(hash, InternedHasher::default())
        }
    }
}

impl<'src, 'intern> Tc<Table<'src, 'intern>> {
    pub fn get(&self, owner: &TCellOwner<TcOwner>, key: &LValue<'src, 'intern>) -> Option<LValue<'src, 'intern>> {
        match key {
            LValue::Number(n) => Some(self.ro(owner).array.get(n.0 as usize-1).cloned().unwrap_or(LValue::Nil)),
            LValue::InternedString(ref s) => {
                self.ro(owner).hash.get(key).cloned()
            },
            LValue::OwnedString(ref s) => {
                self.ro(owner).hash.get(key).cloned()
            },
            _ => unimplemented!()
        }
    }

    pub fn set(&mut self, owner: &mut TCellOwner<TcOwner>, key: LValue<'src, 'intern>, value: LValue<'src, 'intern>) {
        match key {
            LValue::Number(n) => {
                // TODO: sparse arrays
                if self.rw(owner).array.len() <= n.0 as usize {
                    self.rw(owner).array.resize_with(n.0 as usize, || LValue::Nil);
                }
                self.rw(owner).array[n.0 as usize-1] = value
            },
            LValue::InternedString(ref s) => {
                self.rw(owner).hash.insert(key, value);
            },
            LValue::OwnedString(ref s) => {
                self.rw(owner).hash.insert(key, value);
            },
            _ => unimplemented!()
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
    Table(Tc<Table<'src, 'intern>>),
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

    pub fn numeric_op(&self, opcode: Opcode, right: Self) -> Result<LValue<'src, 'intern>, String> {
        // TODO: metamethods
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
            Opcode::ADD => {
                match (self, &right) {
                    (LValue::Number(left_n), LValue::Number(right_n)) =>
                        Ok(LValue::Number(Number(left_n.0 + right_n.0))),
                    _ => unimplemented!(),
                }
            },
            Opcode::SUB => {
                match (self, &right) {
                    (LValue::Number(left_n), LValue::Number(right_n)) =>
                        Ok(LValue::Number(Number(left_n.0 - right_n.0))),
                    _ => unimplemented!(),
                }
            },
            Opcode::MUL => {
                match (self, &right) {
                    (LValue::Number(left_n), LValue::Number(right_n)) =>
                        Ok(LValue::Number(Number(left_n.0 * right_n.0))),
                    x => unimplemented!(),
                }
            },
            Opcode::DIV => {
                match (self, &right) {
                    (LValue::Number(left_n), LValue::Number(right_n)) =>
                        Ok(LValue::Number(Number(left_n.0 / right_n.0))),
                    _ => unimplemented!(),
                }
            },
            Opcode::MOD => {
                match (self, &right) {
                    (LValue::Number(left_n), LValue::Number(right_n)) =>
                        Ok(LValue::Number(Number(left_n.0 % right_n.0))),
                    _ => unimplemented!(),
                }
            },
            Opcode::POW => {
                match (self, &right) {
                    (LValue::Number(left_n), LValue::Number(right_n)) =>
                        Ok(LValue::Number(Number(left_n.0.powf(right_n.0)))),
                    _ => unimplemented!(),
                }
            },
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
enum Upvalue<'src, 'intern> {
    Open(usize), // stack index
    Closed(Gc<LValue<'src, 'intern>>),
}

pub struct LClosure<'src, 'intern> {
    prototype: *const FunctionBlock<'src, LConstant<'src, 'intern>>,
    //environment: LTable<'src>,
    upvalues: FVec<Gc<Upvalue<'src, 'intern>>>,
}

impl<'src, 'intern> Debug for LClosure<'src, 'intern> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "closure(upvalues={:?})", self.upvalues)
    }
}

trait NativeFunc = for<'a, 'src, 'intern> FnMut(&'a [LValue<'src, 'intern>]) -> FVec<LValue<'src, 'intern>>;
struct NClosure {
    native: Box<dyn NativeFunc>,
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
        Tc::new(NClosure { native: Box::new(native) })
    }
}

pub struct Vm<'src, 'intern> {
    // This is terrible, but because we reference FunctionBlocks in Gc<T> types,
    // we can't use proper lifetimes for it: Rust doesn't know that a Gc<T> won't
    // stick around past 'src
    pub top_level: *const FunctionBlock<'src, LConstant<'src, 'intern>>,
}

impl<'src, 'intern> Vm<'src, 'intern> {
    pub fn new(top_level: *const FunctionBlock<'src, LConstant<'src, 'intern>>) -> Self {
        Self { top_level }
    }

    pub fn global_env(&self, owner: &mut TCellOwner<TcOwner>, intern: &'intern internment::Arena<(&'src [u8], u64)>) -> Tc<Table<'src, 'intern>> {
        let mut math_tab = Table::new(0, 0);
        math_tab.hash.insert(InternString::intern(intern, "floor\0"), LValue::NClosure(NClosure::new(|f| {
            let f = match f {
                [LValue::Number(f)] => LValue::Number(Number(f.0.floor())),
                _ => unimplemented!()
            };
            return [f].to_vec().into()
        })));
        math_tab.hash.insert(InternString::intern(intern, "sqrt\0"), LValue::NClosure(NClosure::new(|f| {
            let f = match f {
                [LValue::Number(f)] => LValue::Number(Number(f.0.sqrt())),
                _ => unimplemented!()
            };
            return [f].to_vec().into()
        })));
        math_tab.hash.insert(InternString::intern(intern, "abs\0"), LValue::NClosure(NClosure::new(|f| {
            let f = match f {
                [LValue::Number(f)] => LValue::Number(Number(f.0.abs())),
                _ => unimplemented!()
            };
            return [f].to_vec().into()
        })));
        math_tab.hash.insert(InternString::intern(intern, "huge\0"), LValue::NClosure(NClosure::new(|f| {
            return [LValue::Number(Number(f64::INFINITY))].to_vec().into()
        })));
        math_tab.hash.insert(InternString::intern(intern, "pi\0"), LValue::Number(Number(std::f64::consts::PI)));
        math_tab.hash.insert(InternString::intern(intern, "sin\0"), LValue::NClosure(NClosure::new(|f| {
            let f = match f {
                [LValue::Number(f)] => LValue::Number(Number(f.0.sin())),
                _ => unimplemented!()
            };
            return [f].to_vec().into()
        })));
        math_tab.hash.insert(InternString::intern(intern, "cos\0"), LValue::NClosure(NClosure::new(|f| {
            let f = match f {
                [LValue::Number(f)] => LValue::Number(Number(f.0.cos())),
                _ => unimplemented!()
            };
            return [f].to_vec().into()
        })));
        math_tab.hash.insert(InternString::intern(intern, "tan\0"), LValue::NClosure(NClosure::new(|f| {
            let f = match f {
                [LValue::Number(f)] => LValue::Number(Number(f.0.tan())),
                _ => unimplemented!()
            };
            return [f].to_vec().into()
        })));


        let math = (InternString::intern(intern, "math\0"), LValue::Table(Tc::new(math_tab)));
        Tc::new(Table {
            array: vec![].into(),
            hash: HashMap::<_, _, InternedHasher>::from_iter(
                vec![
                (InternString::intern(intern, "print\0"), LValue::NClosure(NClosure::new(|v| {
                    println!("> {:?}", v);
                    vec![LValue::Nil].into()
                }))),
                math,
                ].drain(..)
            )
        })
    }

    fn rk<'exec>(proto: *const FunctionBlock<'src, LConstant<'src, 'intern>>, base: usize, vals: &'exec FVec<LValue<'src, 'intern>>, r: u16)
        -> Result<&'exec LConstant<'src, 'intern>, &'exec LValue<'src, 'intern>>
    {
        if (r & 0x100)!=0 {
            let r_const = r & (0xff);
            debug!("rk {}", r_const);
            Ok(unsafe { &(*proto).constants.items[r_const as usize] })
        } else {
            Err(&vals[base + r as usize])
        }
    }

    fn close_upvalues<'exec>(&self,
        upvals: &'exec mut FVec<(Upvalue<'src, 'intern>, FVec<Gc<Upvalue<'src, 'intern>>>)>,
        vals: &'exec FVec<LValue<'src, 'intern>>)
    {
        for upval in upvals.iter() {
            let idx = match &upval.0 {
                Upvalue::Open(o) => o,
                Upvalue::Closed(u) => panic!(), // we shouldn't have any closed upvals
            };
            // migrate all the stack references to be GC references, since we're
            // going to be removing it from the stack
            let closed = Gc::new(vals[*idx].clone());
            for up_use in upval.1.iter() {
                up_use.deref().replace(Upvalue::Closed(closed.clone()));
            }
        }
    }

    pub fn run<'lua>(&'lua self,
        owner: &mut TCellOwner<TcOwner>,
        mut _G: Tc<Table<'src, 'intern>>,
        mut clos: Tc<LClosure<'src, 'intern>>,
        mut args: FVec<LValue<'src, 'intern>>,
    )
        -> Result<FVec<LValue<'src, 'intern>>, Box<dyn Error>>
        where 'src: 'lua
    {
        args.resize_with(unsafe {
            (*clos.ro(owner).prototype).max_stack as usize
        }, || LValue::Nil);
        let mut vals = args;
        let mut upvals: FVec<(Upvalue, FVec<Gc<Upvalue>>)> = vec![].into();
        let mut base = 0;
        let mut pc = 0;
        // we need to track where to return to, along with the base pointer and where to put return
        // values
        let mut callstack: FVec<(Tc<LClosure>, usize, usize, usize)> = vec![].into();
        let r_vals = 'int: loop {
            let inst = unsafe { clos.ro(owner).prototype.as_ref().unwrap().instructions.items[pc] };
            pc += 1;
            debug!("pc {} inst {:?}", pc, inst.0.Opcode());
            debug!("stack: {}, {:?}", base, &vals);
            match inst.0.Opcode() {
                Opcode::MOVE => {
                    let (a, b) = <MOVE as Instruction>::Unpack::unpack(inst.0);
                    debug!("move {} {}", a, b);
                    vals[base + a as usize] = vals[base + b as usize].clone();
                },
                Opcode::GETUPVAL => {
                    let (a, b) = <GETUPVAL as Instruction>::Unpack::unpack(inst.0);
                    let upval = match clos.ro(owner).upvalues[b as usize].borrow().deref() {
                        Upvalue::Open(o) => {
                            vals[*o as usize].clone()
                        },
                        Upvalue::Closed(c) => {
                            c.borrow().clone()
                        },
                    };
                    vals[base + a as usize] = upval.clone();
                },
                Opcode::LOADK => {
                    let (a, bx) = <LOADK as Instruction>::Unpack::unpack(inst.0);
                    debug!("loadk {} {} {:?}", a, bx, unsafe { &(*clos.ro(owner).prototype).constants.items[bx as usize] });
                    vals[base + a as usize] = unsafe { (&(*clos.ro(owner).prototype).constants.items[bx as usize]).into() };
                    ()
                },
                Opcode::NEWTABLE => {
                    let (a, b, c) = <NEWTABLE as Instruction>::Unpack::unpack(inst.0);
                    // TODO: properly decode the "floating point byte" size hints instead
                    vals[base + a as usize] = LValue::Table(Tc::new(Table::new(b as usize, c as usize)));
                },
                Opcode::SETLIST => {
                    let (a, b, c) = <SETLIST as Instruction>::Unpack::unpack(inst.0);
                    match vals[base + a as usize].clone() {
                        LValue::Table(tab) => {
                            assert_ne!(c, 0);
                            if b == 0 {
                                let src = vals[base + a as usize+1..].iter().cloned();
                                tab.rw(owner).array.splice(
                                    (c as usize-1)*50..,
                                    src
                                ).for_each(drop);
                            } else {
                                let src = vals[base + a as usize+1..=base + a as usize+b as usize as usize].iter().cloned();
                                tab.rw(owner).array.splice(
                                    (c as usize-1)*50..,
                                    src
                                ).for_each(drop);
                            }
                        },
                        _ => unimplemented!(),
                    }
                },
                Opcode::GETTABLE => {
                    let (a, b, c) = <GETTABLE as Instruction>::Unpack::unpack(inst.0);
                    debug!("gettable {} {} {}", a, b, c);
                    let kc = match Self::rk(clos.ro(owner).prototype, base, &vals, c) {
                        Ok(c) => Cow::Owned(LValue::from(c)),
                        Err(lv) => Cow::Borrowed(lv),
                    };
                    debug!("gettable {:?}", &kc);
                    let val_b = match &vals[base + b as usize] {
                        LValue::Table(tab) => {
                            debug!("table {:?}", tab);
                            tab.get(owner, kc.deref()).ok_or_else(|| Err::<LValue, String>(format!("{:?}", kc))).unwrap()
                        },
                        x => unimplemented!("gettable on {:?}", x),
                    };
                    debug!("gettable {:?}", &val_b);
                    vals[base + a as usize] = val_b;
                },
                Opcode::SETTABLE => {
                    let (a, b, c) = <SETTABLE as Instruction>::Unpack::unpack(inst.0);
                    debug!("settable {} {} {}", a, b, c);
                    let kb = match Self::rk(clos.ro(owner).prototype, base, &vals, b) {
                        Ok(b) => b.into(),
                        Err(lv) => lv.clone(),
                    };
                    debug!("settable {:?}", &kb);
                    let kc = match Self::rk(clos.ro(owner).prototype, base, &vals, c) {
                        Ok(c) => c.into(),
                        Err(lv) => lv.clone(),
                    };
                    match &mut vals[base + a as usize] {
                        LValue::Table(tab) => {
                            tab.set(owner, kb, kc)
                        },
                        x => { debug!("huh {:?}", x); unimplemented!() },
                    };
                },
                Opcode::SETGLOBAL => {
                    let (a, bx) = <SETGLOBAL as Instruction>::Unpack::unpack(inst.0);
                    let kst = unsafe { &(*clos.ro(owner).prototype).constants.items[bx as usize] };
                    debug!("setglobal {} {} {:?}", a, bx, &kst);
                    _G.set(owner, kst.into(), vals[base + a as usize].clone());
                },
                Opcode::GETGLOBAL => {
                    let (a, bx) = <SETGLOBAL as Instruction>::Unpack::unpack(inst.0);
                    let kst = unsafe { &(*clos.ro(owner).prototype).constants.items[bx as usize] };
                    debug!("getglobal {} {} {:?}", a, bx, &kst);
                    // FIXME(error handling)
                    vals[base + a as usize] = _G.get(owner, &kst.into()).unwrap_or((&Constant::Nil).into()).clone();
                },
                opcode @ (Opcode::EQ | Opcode::LT | Opcode::LE) => {
                    let (a, b, c) = ABC::unpack(inst.0);
                    debug!("numeric op {} {}", b, c);
                    let kb = Self::rk(clos.ro(owner).prototype, base, &vals, b);
                    let kc = Self::rk(clos.ro(owner).prototype, base, &vals, c);
                    debug!("{:?} {:?}", &kb, &kc);
                    let cond = match (opcode, kb, kc) {
                        (Opcode::EQ, Ok(const_b), Ok(const_c)) => const_b == const_c,
                        (Opcode::LT, Ok(const_b), Ok(const_c)) => const_b < const_c,
                        (Opcode::LE, Ok(const_b), Ok(const_c)) => const_b <= const_c,

                        (_, Err(dyn_b), Ok(const_c)) => {
                            dyn_b.compare(opcode.clone(), const_c.into()).unwrap()
                        },

                        (_, Ok(const_b), Err(dyn_c)) => {
                            LValue::from(const_b).compare(opcode, dyn_c.clone()).unwrap()
                        },

                        (_, Err(dyn_b), Err(dyn_c)) => {
                            dyn_b.compare(opcode, dyn_c.clone()).unwrap()
                        },

                        _ => panic!()

                    };
                    debug!("cond {} {}", cond, a);
                    if (cond as u8) != a {
                        pc += 1;
                    }
                },
                opcode @ (Opcode::ADD | Opcode::SUB | Opcode::MUL | Opcode::DIV | Opcode::MOD | Opcode::POW)
                => {
                    let (a, b, c) = ABC::unpack(inst.0);
                    debug!("{} {} {}", a, b, c);
                    let kb = Self::rk(clos.ro(owner).prototype, base, &vals, b);
                    let kc = Self::rk(clos.ro(owner).prototype, base, &vals, c);
                    debug!("{:?} {:?}", &kb, &kc);
                    let res = match (opcode, kb, kc) {
                        (Opcode::ADD, Ok(Constant::Number(const_b)), Ok(Constant::Number(const_c))) =>
                            LValue::Number(Number(const_b.0 + const_c.0)),
                        (Opcode::SUB, Ok(Constant::Number(const_b)), Ok(Constant::Number(const_c))) =>
                            LValue::Number(Number(const_b.0 - const_c.0)),
                        (Opcode::MUL, Ok(Constant::Number(const_b)), Ok(Constant::Number(const_c))) =>
                            LValue::Number(Number(const_b.0 * const_c.0)),
                        (Opcode::DIV, Ok(Constant::Number(const_b)), Ok(Constant::Number(const_c))) =>
                            LValue::Number(Number(const_b.0 / const_c.0)),
                        (Opcode::MOD, Ok(Constant::Number(const_b)), Ok(Constant::Number(const_c))) =>
                            LValue::Number(Number(const_b.0 % const_c.0)),
                        (Opcode::POW, Ok(Constant::Number(const_b)), Ok(Constant::Number(const_c))) =>
                            LValue::Number(Number(const_b.0.powf(const_c.0))),

                        (_, Ok(const_b), Err(dyn_c)) => {
                            LValue::from(const_b).numeric_op(opcode, dyn_c.clone().into())?
                        },

                        (_, Err(dyn_b), Ok(const_c)) => {
                            dyn_b.numeric_op(opcode, const_c.into())?
                        },

                        (_, Err(dyn_b), Err(dyn_c)) => {
                            dyn_b.numeric_op(opcode, dyn_c.clone().into())?
                        },

                        _ => unimplemented!(),
                    };
                    debug!("res {:?}", &res);
                    vals[base + a as usize] = res;
                },
                Opcode::UNM => {
                    let (a, b) = <UNM as Instruction>::Unpack::unpack(inst.0);
                    let res = match &vals[base + b as usize] {
                        // TODO: metatables
                        LValue::Number(n) => LValue::Number(Number(-n.0)),
                        _ => unimplemented!(),
                    };
                    vals[base + a as usize] = res;
                },
                Opcode::LEN => {
                    let (a, b) = <LEN as Instruction>::Unpack::unpack(inst.0);
                    debug!("{} {}", a, b);
                    vals[base + a as usize] = vals[base + b as usize].len(owner)?;
                },
                Opcode::FORPREP => {
                    let (a, sbx) = <FORPREP as Instruction>::Unpack::unpack(inst.0);
                    debug!("{} {}", a, sbx);
                    vals[base + a as usize] =
                        vals[base + a as usize].numeric_op(Opcode::SUB, vals[base + a as usize + 2].clone()).unwrap();
                    pc += sbx as usize;
                },
                Opcode::FORLOOP => {
                    let (a, sbx) = <FORLOOP as Instruction>::Unpack::unpack(inst.0);
                    debug!("{} {}", a, sbx);
                    let step = vals[base + a as usize + 2].clone();
                    let idx = vals[base + a as usize].numeric_op(Opcode::ADD, step.clone()).unwrap();
                    let limit = vals[base + a as usize + 1].clone();
                    let comp = if step.compare(Opcode::LT, LValue::from(&Constant::Number(Number(0.0))))? {
                        limit.compare(Opcode::LE, idx.clone())
                    } else {
                        idx.clone().compare(Opcode::LE, limit)
                    };
                    if comp? {
                        pc = (pc as isize + sbx as isize) as usize;
                        vals[base + a as usize] = idx.clone();
                        vals[base + a as usize + 3] = idx;
                    }
                },
                Opcode::JMP => {
                    debug!("{:?}", inst.0);
                    let sbx = <JMP as Instruction>::Unpack::unpack(inst.0);
                    debug!("{}", sbx);
                    pc += sbx as usize;
                },
                Opcode::CLOSURE => {
                    let (a, bx) = <CLOSURE as Instruction>::Unpack::unpack(inst.0);
                    let proto = unsafe { &(*clos.ro(owner).prototype).prototypes.items[bx as usize] };
                    debug!("{} {} {:?}", a, bx, proto);
                    // handle the MOVE/GETUPVALUE pseudoinstructions
                    let mut fresh = LClosure::new(proto as *const _);
                    {
                        for upval in 0..proto.upval_count {
                            let pseudo = unsafe { (*clos.ro(owner).prototype).instructions.items[pc+upval as usize] };
                            let label = match pseudo.0.Opcode() {
                                Opcode::MOVE => {
                                    let (_, b) = <MOVE as Instruction>::Unpack::unpack(pseudo.0);
                                    // we can't just copy vals[b], because we need
                                    // to reference the stack slot not the value.
                                    // instead we reference the stack slot, and add
                                    // this new use to the list of uses. on CLOSE
                                    // we will iterate over all these uses and close
                                    // them - but only then.
                                    let fresh_upval = Upvalue::Open(b as usize);
                                    let fresh_use = Gc::new(fresh_upval.clone());
                                    fresh.upvalues.push(fresh_use.clone());
                                    upvals.push((fresh_upval, vec![fresh_use].into()));
                                    "move"
                                },
                                Opcode::GETUPVAL => {
                                    let (_, b) = <GETUPVAL as Instruction>::Unpack::unpack(pseudo.0);
                                    // the upvalue already exists in our current
                                    // scope. add ourselves to the existing
                                    // use list.
                                    let fresh_use = Gc::new(upvals[b as usize].clone().0);
                                    fresh.upvalues.push(fresh_use.clone());
                                    upvals[b as usize].1.push(fresh_use);
                                    "getupvval"
                                },
                                _ => panic!(),
                            };
                            debug!("pseudo: {:?} ({})", pseudo, label);
                        }
                        pc += proto.upval_count as usize;
                        //assert_eq!(proto.upval_count, 0);
                    }
                    vals[base + a as usize] = LValue::LClosure(Tc::new(fresh));
                },
                Opcode::CALL => {
                    let (a, b, c) = <CALL as Instruction>::Unpack::unpack(inst.0);
                    debug!("{} {} {}", a, b, c);
                    let to_call = &vals[base + a as usize];
                    debug!("{:?}", to_call);
                    // push where to return to once we RETURN
                    if let LValue::LClosure(ref lclos) = to_call.clone() {
                        // record call stack: we say where to return to and where to put the values
                        callstack.push((clos.clone(), pc, base, base + a as usize));
                        clos = lclos.clone();
                        let next_stack = unsafe { (*lclos.ro(owner).prototype).max_stack as usize };
                        base = base + a as usize + 1;
                        // push empty stack frame
                        vals.extend_from_slice(
                            vec![LValue::Nil; next_stack].as_slice());
                        pc = 0;
                    } else if let LValue::NClosure(ncall) = to_call {
                        let args = if b == 0 {
                            &vals[base + a as usize+1..]
                        } else {
                            &vals[base + a as usize+1..=(base + a as usize + b as usize - 1)]
                        };
                        debug!("{:?}", args);
                        let ret = (ncall.rw(owner).native)(args);
                        if c == 0 {
                            // save all returned
                            vals.splice(base + a as usize.., ret).for_each(drop);
                        }
                        else if c == 1 {
                            // nothing saved
                        } else if c != 1 {
                            vals.splice(base + a as usize..base + a as usize + c as usize - 2, ret).for_each(drop);
                        } else {
                            unimplemented!()
                        }
                        // FIXME(metatables): __call
                    }
                },
                Opcode::RETURN => {
                    // we're going to be removing this frame, so close any open
                    // upvalues.
                    self.close_upvalues(&mut upvals, &vals);
                    upvals = vec![].into();

                    let (a, b) = <RETURN as Instruction>::Unpack::unpack(inst.0);
                    debug!("{} {}", a, b);
                    let mut r_count = 0 as usize;
                    let mut r_vals: FVec<_> = if b == 1 {
                        // no return values
                        vec![].into()
                    } else if b >= 2 {
                        // there are b-1 return values from R(A) onwards
                        r_count = b as usize-1;
                        let r_vals = &vals[base + a as usize..(base + a as usize + r_count as usize)];
                        debug!("{:?}", r_vals);
                        Vec::from(r_vals).into()
                    } else if b == 0 {
                        // return all values from R(A) to the ToS
                        let r_vals = &vals[base + a as usize..];
                        r_count = r_vals.len() as usize;
                        debug!("{:?}", r_vals);
                        Vec::from(r_vals).into()
                    } else {
                        unreachable!()
                    };
                    if let Some((ret_clos, caller, frame, ret)) = callstack.pop() {
                        debug!("{:?} {:?}", unsafe { &(*ret_clos.ro(owner).prototype).instructions }, caller);
                        clos = ret_clos.clone();
                        // copy the return values to the previous frame's return location,
                        // then clean up the popped stack frame
                        base = frame;
                        let parent_stack = unsafe { (*clos.ro(owner).prototype).max_stack as usize };
                        //vals.extend_from_slice(r_vals.as_slice());
                        for (i, v) in r_vals.drain(..).enumerate() {
                            vals[ret + i] = v;
                        }
                        vals.truncate(frame + parent_stack);
                        pc = caller;
                    } else {
                        break 'int r_vals;
                    }
                },
                Opcode::INVALID => unreachable!(),
                x => unimplemented!("opcode {:?}", x),
                _ => (),
            };
        };
        Ok(r_vals)
    }
}
