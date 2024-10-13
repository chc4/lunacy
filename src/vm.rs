#![allow(non_snake_case)]
use crate::chunk::FunctionBlock;
use core::fmt::Debug;
use core::hash::Hash;
use std::{error::Error, rc::Rc, ops::Deref};
use rustc_hash::FxHashMap;
use std::cell::{RefCell, Cell};
use std::borrow::Cow;
use crate::chunk::{Constant, InstBits};

use log::debug;

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


#[derive(Debug)]
struct Gc<T>(Rc<RefCell<T>>);

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

#[derive(Debug)]
struct Table<'lua, 'src> {
    array: Vec<LValue<'lua, 'src>>,
    hash: FxHashMap<LValue<'lua, 'src>, LValue<'lua, 'src>>,
}

impl<'lua, 'src> Table<'lua, 'src> {
    pub fn new(array: usize, hash: usize) -> Self {
        Self {
            array: vec![LValue::Nil; array],
            hash: FxHashMap::with_capacity_and_hasher(hash, Default::default())
        }
    }
}

impl<'lua, 'src> Gc<Table<'lua, 'src>> {
    fn get(&self, key: LValue<'lua, 'src>) -> Option<LValue<'lua, 'src>> {
        match key {
            LValue::Number(n) => Some(self.borrow().array.get(n.0 as usize-1).cloned().unwrap_or(LValue::Nil)),
            LValue::String(_) => {
                self.borrow().hash.get(&key).cloned()
            },
            _ => unimplemented!()
        }
    }

    fn set(&mut self, key: LValue<'lua, 'src>, value: LValue<'lua, 'src>) {
        match key {
            LValue::Number(n) => unimplemented!(),
            LValue::String(_) => {
                self.borrow_mut().hash.insert(key, value);
            },
            _ => unimplemented!()
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum LValue<'lua, 'src> {
    Nil,
    Bool(bool),
    Number(Number),
    String(Cow<'src, [u8]>),
    Closure(Closure<'lua, 'src>),
    Table(Gc<Table<'lua, 'src>>),
}

impl<'lua, 'src> LValue<'lua, 'src> {
    #[inline]
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
            (LValue::Closure(left_c), LValue::Closure(right_c)) => {
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
                    (LValue::String(left_s), LValue::String(right_s)) => Ok(left_s < right_s),
                    _ => panic!()
                }
            },
            Opcode::LE => {
                match (self, &right) {
                    (LValue::Bool(left_b), LValue::Bool(right_b)) => Ok(left_b <= right_b),
                    (LValue::Number(left_n), LValue::Number(right_n)) => Ok(left_n <= right_n),
                    (LValue::String(left_s), LValue::String(right_s)) => Ok(left_s <= right_s),
                    _ => panic!()
                }

            },
            _ => panic!()
        }
    }

    #[inline]
    pub fn numeric_op(&self, opcode: Opcode, right: Self) -> Result<LValue<'lua, 'src>, String> {
        // TODO: metamethods
        match (self, &right) {
            (LValue::Nil, LValue::Nil) => {
                return Err("attempt to compare nil".into())
            },
            (LValue::Table(left_tab), LValue::Table(right_tab)) => {
                unimplemented!("metamethod")
            },
            (LValue::Closure(left_c), LValue::Closure(right_c)) => {
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
                    _ => unimplemented!(),
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

    pub fn len(&self) -> Result<LValue<'lua, 'src>, String> {
        // TODO: metamethods
        match self {
            LValue::String(s) => Ok(LValue::Number(Number(s.len() as _))),
            LValue::Table(t) => {
                // TODO: sparse arrays
                Ok(LValue::Number(Number(t.0.borrow_mut().array.len() as _)))
            },
            _ => unimplemented!(),
        }
    }
}

impl<'lua, 'src> From<Constant<'src>> for LValue<'src, 'src> {
    fn from(value: Constant<'src>) -> Self {
        match value {
            Constant::Nil => LValue::Nil,
            Constant::Bool(b) => LValue::Bool(b),
            Constant::Number(i) => LValue::Number(i),
            Constant::String(s) => LValue::String(Cow::Borrowed(s.data)),
        }
    }
}

#[derive(Debug, Clone)]
enum Upvalue<'lua, 'src> {
    Open(usize), // stack index
    Closed(Gc<LValue<'lua, 'src>>),
}

struct LClosure<'lua, 'src> {
    prototype: &'lua FunctionBlock<'src>,
    //environment: LTable<'src>,
    upvalues: Vec<Gc<Upvalue<'lua, 'src>>>,
}

impl<'lua, 'src> Debug for LClosure<'lua, 'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "closure(upvalues={:?})", self.upvalues)
    }
}

trait NativeFunc = for<'a, 'lua, 'src> FnMut(&'a [LValue<'lua, 'src>]) -> Vec<LValue<'lua, 'src>>;
struct NClosure {
    native: Box<dyn NativeFunc>,
}

impl<'lua, 'src> Debug for NClosure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<native function {:p}>", self.native.as_ref())
    }
}

impl<'lua, 'src> LClosure<'lua, 'src> {
    fn new(prototype: &'lua FunctionBlock<'src>) -> Self {
        Self {
            prototype,
            upvalues: vec![],
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Closure<'lua, 'src> {
    Lua(Gc<LClosure<'lua, 'src>>),
    Native(Gc<NClosure>),
}

impl<'lua, 'src> Closure<'lua, 'src> {
    pub fn from_lua(prototype: &'lua FunctionBlock<'src>) -> Self {
        Self::Lua(Gc::new(LClosure::new(prototype)))
    }

    pub fn into_lua(&self) -> std::cell::RefMut<'_, LClosure<'lua, 'src>> {
        if let Closure::Lua(clos) = self {
            clos.borrow_mut()
        } else {
            panic!()
        }
    }

    pub fn from_native(native: impl NativeFunc + 'static) -> Self {
        Self::Native(Gc::new(NClosure { native: Box::new(native) }))
    }
}

pub struct Vm<'src> {
    top_level: FunctionBlock<'src>,
}

impl<'src> Vm<'src> {
    pub fn new(top_level: FunctionBlock<'src>) -> Self {
        Self { top_level }
    }

    fn global_env(&self) -> Gc<Table> {
        let mut math_tab = Table::new(0, 0);
        math_tab.hash.insert(LValue::String("floor\0".as_bytes().into()), LValue::Closure(Closure::from_native(|f| {
            let f = match f {
                [LValue::Number(f)] => LValue::Number(Number(f.0.floor())),
                _ => unimplemented!()
            };
            return [f].to_vec()
        })));
        math_tab.hash.insert(LValue::String("sqrt\0".as_bytes().into()), LValue::Closure(Closure::from_native(|f| {
            let f = match f {
                [LValue::Number(f)] => LValue::Number(Number(f.0.sqrt())),
                _ => unimplemented!()
            };
            return [f].to_vec()
        })));
        math_tab.hash.insert(LValue::String("abs\0".as_bytes().into()), LValue::Closure(Closure::from_native(|f| {
            let f = match f {
                [LValue::Number(f)] => LValue::Number(Number(f.0.abs())),
                _ => unimplemented!()
            };
            return [f].to_vec()
        })));


        let math = (LValue::String("math\0".as_bytes().into()), LValue::Table(Gc::new(math_tab)));
        Gc::new(Table {
            array: vec![],
            hash: FxHashMap::from_iter(
                vec![
                (LValue::String("print\0".as_bytes().into()), LValue::Closure(Closure::from_native(|v| {
                    println!("> {:?}", v);
                    vec![LValue::Nil]
                }))),
                math,
                ].drain(..)
            )
        })
    }

    fn rk<'a, 'b>(proto: &'a FunctionBlock<'src>, base: usize, vals: &'b Vec<LValue<'a, 'src>>, r: u16) -> Result<&'a Constant<'a>, LValue<'a, 'src>> {
        if (r & 0x100)!=0 {
            let r_const = r & (0xff);
            debug!("rk {}", r_const);
            Ok(&proto.constants.items[r_const as usize])
        } else {
            Err(vals[base + r as usize].clone())
        }
    }

    fn close_upvalues<'lua>(&self, upvals: &mut Vec<(Upvalue<'lua, 'src>, Vec<Gc<Upvalue<'lua, 'src>>>)>, vals: &Vec<LValue<'lua, 'src>>) {
        for upval in upvals {
            let idx = match &upval.0 {
                Upvalue::Open(o) => o,
                Upvalue::Closed(u) => panic!(), // we shouldn't have any closed upvals
            };
            // migrate all the stack references to be GC references, since we're
            // going to be removing it from the stack
            let closed = Gc::new(vals[*idx].clone());
            for up_use in &upval.1 {
                up_use.deref().replace(Upvalue::Closed(closed.clone()));
            }
        }
    }

    pub fn run<'a>(&'a mut self) -> Result<Vec<LValue<'a, 'src>>, Box<dyn Error>> where 'a: 'src {
        let mut _G = self.global_env();
        // we should create a new closure for the top_level and run that instead
        let mut clos = Closure::from_lua(&self.top_level);
        let mut vals: Vec<LValue> = vec![LValue::from(Constant::Nil); clos.into_lua().prototype.max_stack as usize];
        let mut upvals: Vec<(Upvalue, Vec<Gc<Upvalue>>)> = vec![];
        let mut base = 0;
        let mut pc = 0;
        // we need to track where to return to, along with the base pointer and where to put return
        // values
        let mut callstack: Vec<(Closure, usize, usize, usize)> = vec![];
        let r_vals = 'int: loop {
            let inst = clos.into_lua().prototype.instructions.items[pc];
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
                    let upval = match clos.into_lua().upvalues[b as usize].borrow().deref() {
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
                    debug!("loadk {} {} {:?}", a, bx, &clos.into_lua().prototype.constants.items[bx as usize]);
                    vals[base + a as usize] = clos.into_lua().prototype.constants.items[bx as usize].clone().into();
                    ()
                },
                Opcode::NEWTABLE => {
                    let (a, b, c) = <NEWTABLE as Instruction>::Unpack::unpack(inst.0);
                    vals[base + a as usize] = LValue::Table(Gc::new(Table::new(b as usize, c as usize)));
                },
                Opcode::SETLIST => {
                    let (a, b, c) = <SETLIST as Instruction>::Unpack::unpack(inst.0);
                    match vals[base + a as usize].clone() {
                        LValue::Table(tab) => {
                            assert_ne!(c, 0);
                            if b == 0 {
                                let src = vals[base + a as usize+1..].iter().cloned();
                                tab.borrow_mut().array.splice(
                                    (c as usize-1)*50..,
                                    src
                                ).for_each(drop);
                            } else {
                                let src = vals[base + a as usize+1..=base + a as usize+b as usize as usize].iter().cloned();
                                tab.borrow_mut().array.splice(
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
                    let clos = clos.into_lua();
                    let kc = match Self::rk(clos.prototype, base, &vals, c) {
                        Ok(c) => c.clone().into(),
                        Err(lv) => lv,
                    };
                    debug!("gettable {:?}", &kc);
                    let val_b = match &vals[base + b as usize] {
                        LValue::Table(tab) => {
                            debug!("table {:?}", tab);
                            tab.get(kc.clone()).ok_or_else(|| Err::<LValue, String>(format!("{:?}", kc))).unwrap()
                        },
                        x => unimplemented!("gettable on {:?}", x),
                    };
                    debug!("gettable {:?}", &val_b);
                    vals[base + a as usize] = val_b;
                },
                Opcode::SETTABLE => {
                    let (a, b, c) = <SETTABLE as Instruction>::Unpack::unpack(inst.0);
                    debug!("settable {} {} {}", a, b, c);
                    let clos = clos.into_lua();
                    let kb = match Self::rk(clos.prototype, base, &vals, b) {
                        Ok(b) => b.clone().into(),
                        Err(lv) => lv,
                    };
                    debug!("settable {:?}", &kb);
                    let kc = match Self::rk(clos.prototype, base, &vals, c) {
                        Ok(c) => c.clone().into(),
                        Err(lv) => lv,
                    };
                    match &mut vals[base + a as usize] {
                        LValue::Table(tab) => {
                            tab.set(kb, kc)
                        },
                        _ => unimplemented!(),
                    };
                },
                Opcode::SETGLOBAL => {
                    let (a, bx) = <SETGLOBAL as Instruction>::Unpack::unpack(inst.0);
                    let kst = &clos.into_lua().prototype.constants.items[bx as usize];
                    debug!("setglobal {} {} {:?}", a, bx, &kst);
                    _G.set(kst.clone().into(), vals[base + a as usize].clone());
                },
                Opcode::GETGLOBAL => {
                    let (a, bx) = <SETGLOBAL as Instruction>::Unpack::unpack(inst.0);
                    let kst = &clos.into_lua().prototype.constants.items[bx as usize];
                    debug!("getglobal {} {} {:?}", a, bx, &kst);
                    // FIXME(error handling)
                    vals[base + a as usize] = _G.get(kst.clone().into()).unwrap_or(Constant::Nil.into()).clone();
                },
                opcode @ (Opcode::EQ | Opcode::LT | Opcode::LE) => {
                    let (a, b, c) = ABC::unpack(inst.0);
                    debug!("numeric op {} {}", b, c);
                    let kb = Self::rk(clos.into_lua().prototype, base, &vals, b);
                    let kc = Self::rk(clos.into_lua().prototype, base, &vals, c);
                    debug!("{:?} {:?}", &kb, &kc);
                    let cond = match (opcode, kb, kc) {
                        (Opcode::EQ, Ok(const_b), Ok(const_c)) => const_b == const_c,
                        (Opcode::LT, Ok(const_b), Ok(const_c)) => const_b < const_c,
                        (Opcode::LE, Ok(const_b), Ok(const_c)) => const_b <= const_c,

                        (_, Err(dyn_b), Ok(const_c)) => {
                            dyn_b.compare(opcode.clone(), const_c.clone().into()).unwrap()
                        },

                        (_, Ok(const_b), Err(dyn_c)) => {
                            LValue::from(const_b.clone()).compare(opcode, dyn_c).unwrap()
                        },

                        (_, Err(dyn_b), Err(dyn_c)) => {
                            dyn_b.compare(opcode, dyn_c).unwrap()
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
                    let kb = Self::rk(clos.into_lua().prototype, base, &vals, b);
                    let kc = Self::rk(clos.into_lua().prototype, base, &vals, c);
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
                            LValue::from(const_b.clone()).numeric_op(opcode, dyn_c.into())?
                        },

                        (_, Err(dyn_b), Ok(const_c)) => {
                            dyn_b.numeric_op(opcode, const_c.clone().into())?
                        },

                        (_, Err(dyn_b), Err(dyn_c)) => {
                            dyn_b.numeric_op(opcode, dyn_c.into())?
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
                    vals[base + a as usize] = vals[base + b as usize].len()?;
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
                    let comp = if step.compare(Opcode::LT, LValue::from(Constant::Number(Number(0.0))))? {
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
                    let clos = clos.into_lua();
                    let proto = &clos.prototype.prototypes.items[bx as usize];
                    debug!("{} {} {:?}", a, bx, proto);
                    // handle the MOVE/GETUPVALUE pseudoinstructions
                    let fresh = Closure::from_lua(proto);
                    {
                        let mut fresh_clos = fresh.into_lua();
                        for upval in 0..proto.upval_count {
                            let pseudo = clos.prototype.instructions.items[pc+upval as usize];
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
                                    fresh_clos.upvalues.push(fresh_use.clone());
                                    upvals.push((fresh_upval, vec![fresh_use]));
                                    "move"
                                },
                                Opcode::GETUPVAL => {
                                    let (_, b) = <GETUPVAL as Instruction>::Unpack::unpack(pseudo.0);
                                    // the upvalue already exists in our current
                                    // scope. add ourselves to the existing
                                    // use list.
                                    let fresh_use = Gc::new(upvals[b as usize].clone().0);
                                    fresh_clos.upvalues.push(fresh_use.clone());
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
                    vals[base + a as usize] = LValue::Closure(fresh);
                },
                Opcode::CALL => {
                    let (a, b, c) = <CALL as Instruction>::Unpack::unpack(inst.0);
                    debug!("{} {} {}", a, b, c);
                    let to_call = &vals[base + a as usize];
                    debug!("{:?}", to_call);
                    // push where to return to once we RETURN
                    if let LValue::Closure(ref lcall @ Closure::Lua(ref lclos)) = to_call.clone() {
                        // record call stack: we say where to return to and where to put the values
                        callstack.push((clos.clone(), pc, base, base + a as usize));
                        clos = lcall.clone();
                        let next_stack = lcall.into_lua().prototype.max_stack as usize;
                        base = base + a as usize + 1;
                        // push empty stack frame
                        vals.extend_from_slice(
                            vec![LValue::Nil; next_stack].as_slice());
                        pc = 0;
                    } else if let LValue::Closure(Closure::Native(ncall)) = to_call {
                        let args = if b == 0 {
                            &vals[base + a as usize+1..]
                        } else {
                            &vals[base + a as usize+1..=(base + a as usize + b as usize - 1)]
                        };
                        debug!("{:?}", args);
                        let ret = (ncall.borrow_mut().native)(args);
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
                    upvals = vec![];

                    let (a, b) = <RETURN as Instruction>::Unpack::unpack(inst.0);
                    debug!("{} {}", a, b);
                    let mut r_count = 0 as usize;
                    let mut r_vals = if b == 1 {
                        // no return values
                        vec![]
                    } else if b >= 2 {
                        // there are b-1 return values from R(A) onwards
                        r_count = b as usize-1;
                        let r_vals = &vals[base + a as usize..(base + a as usize + r_count as usize)];
                        debug!("{:?}", r_vals);
                        Vec::from(r_vals)
                    } else if b == 0 {
                        // return all values from R(A) to the ToS
                        let r_vals = &vals[base + a as usize..];
                        r_count = r_vals.len() as usize;
                        debug!("{:?}", r_vals);
                        Vec::from(r_vals)
                    } else {
                        unreachable!()
                    };
                    if let Some((ret_clos, caller, frame, ret)) = callstack.pop() {
                        debug!("{:?} {:?}", &ret_clos.into_lua().prototype.instructions, caller);
                        clos = ret_clos;
                        // copy the return values to the previous frame's return location,
                        // then clean up the popped stack frame
                        base = frame;
                        let parent_stack = clos.into_lua().prototype.max_stack as usize;
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
