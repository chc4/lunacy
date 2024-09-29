use crate::chunk::FunctionBlock;
use core::fmt::Debug;
use core::hash::Hash;
use std::{error::Error, rc::Rc, ops::Deref};
use std::collections::HashMap;
use std::cell::RefCell;
use crate::chunk::{Constant, InstBits};

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Number(pub f64);

impl Hash for Number {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.0.to_bits())
    }
}

impl Eq for Number {
}

#[repr(u8)]
#[derive(Debug)]
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

struct MOVE;
impl Instruction for MOVE { type Unpack = AB; }

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
    hash: HashMap<LValue<'lua, 'src>, LValue<'lua, 'src>>,
}

impl<'lua, 'src> Gc<Table<'lua, 'src>> {
    fn get(&self, key: LValue<'lua, 'src>) -> Option<LValue<'lua, 'src>> {
        match key {
            LValue::Number(n) => unimplemented!(),
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
    String(String),
    Closure(Closure<'lua, 'src>),
    Table(Gc<Table<'lua, 'src>>),
}

impl<'lua, 'src> From<Constant<'src>> for LValue<'src, 'src> {
    fn from(value: Constant) -> Self {
        match value {
            Constant::Nil => LValue::Nil,
            Constant::Bool(b) => LValue::Bool(b),
            Constant::Number(i) => LValue::Number(i),
            Constant::String(s) => LValue::String(String::from_utf8_lossy(s.data).into_owned()),
        }
    }
}

enum Upvalue<'lua, 'src> {
    Open(&'lua LValue<'lua, 'src>),
    Closed(LValue<'lua, 'src>),
}

#[derive(Debug)]
struct LClosure<'lua, 'src> {
    prototype: &'lua FunctionBlock<'src>,
    //environment: LTable<'src>,
    //upvalues: Vec<Upvalue<'lua>>,
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
            prototype
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
        Gc::new(Table {
            array: vec![],
            hash: HashMap::from_iter(
                vec![(LValue::String("print\0".into()), LValue::Closure(Closure::from_native(|v| {
                    println!("> {:?}", v);
                    vec![LValue::Nil]
                })))].drain(..)
            )
        })
    }

    fn rk<'a, 'b>(proto: &'a FunctionBlock<'src>, vals: &'b Vec<LValue<'a, 'src>>, r: u16) -> Result<Constant<'a>, LValue<'a, 'src>> {
        if (r & 2^9)!=0 {
            let r_const = r & ((2^8)-1);
            dbg!(r_const);
            Ok(proto.constants.items[r_const as usize].clone())
        } else {
            Err(vals[r as usize].clone())
        }
    }

    pub fn run<'a>(&'a mut self) -> Result<Vec<LValue<'a, 'src>>, Box<dyn Error>> where 'a: 'src {
        let mut _G = self.global_env();
        // we should create a new closure for the top_level and run that instead
        let mut clos = Closure::from_lua(&self.top_level);
        let mut vals: Vec<LValue> = vec![LValue::from(Constant::Nil); clos.into_lua().prototype.max_stack as usize];
        let mut pc = 0;
        // we need to track where to return to
        let mut callstack: Vec<(Closure, usize)> = vec![];
        let r_vals = 'int: loop {
            let inst = clos.into_lua().prototype.instructions.items[pc];
            pc += 1;
            println!("inst {:?}", inst.0.Opcode());
            match inst.0.Opcode() {
                Opcode::MOVE => {
                    let (a, b) = <MOVE as Instruction>::Unpack::unpack(inst.0);
                    dbg!(a, b);
                    vals[a as usize] = vals[b as usize].clone();
                },
                Opcode::LOADK => {
                    let (a, bx) = <LOADK as Instruction>::Unpack::unpack(inst.0);
                    dbg!(a, bx, &clos.into_lua().prototype.constants.items[bx as usize]);
                    vals[a as usize] = clos.into_lua().prototype.constants.items[bx as usize].clone().into();
                    ()
                },
                Opcode::SETGLOBAL => {
                    let (a, bx) = <SETGLOBAL as Instruction>::Unpack::unpack(inst.0);
                    let kst = &clos.into_lua().prototype.constants.items[bx as usize];
                    dbg!(a, bx, &kst);
                    _G.set(kst.clone().into(), vals[a as usize].clone());
                },
                Opcode::GETGLOBAL => {
                    let (a, bx) = <SETGLOBAL as Instruction>::Unpack::unpack(inst.0);
                    let kst = &clos.into_lua().prototype.constants.items[bx as usize];
                    dbg!(a, bx, &kst);
                    // FIXME(error handling)
                    vals[a as usize] = _G.get(kst.clone().into()).unwrap_or(Constant::Nil.into()).clone();
                },
                Opcode::EQ => {
                    let (a, b, c) = ABC::unpack(inst.0);
                    dbg!(b, c);
                    let kb = Self::rk(clos.into_lua().prototype, &vals, b);
                    let kc = Self::rk(clos.into_lua().prototype, &vals, c);
                    dbg!(&kb, &kc);
                    let cond = match (kb, kc) {
                        (Ok(const_b), Ok(const_c)) => const_b == const_c,
                        (Err(dyn_val), Ok(const_val)) | (Ok(const_val), Err(dyn_val)) => {
                            dyn_val == const_val.into()
                        },
                        (Err(dyn_b), Err(dyn_c)) => {
                            dyn_b == dyn_c
                        }
                    };
                    dbg!(cond, a);
                    if (cond as u8) != a {
                        pc += 1;
                    }
                },
                Opcode::JMP => {
                    dbg!(inst.0);
                    let sbx = <JMP as Instruction>::Unpack::unpack(inst.0);
                    dbg!(sbx);
                    pc += sbx as usize;
                },
                Opcode::CLOSURE => {
                    let (a, bx) = <CLOSURE as Instruction>::Unpack::unpack(inst.0);
                    let proto = &clos.into_lua().prototype.prototypes.items[bx as usize];
                    dbg!(a, bx, proto);
                    // we'd need to handle the MOVE/GETUPVALUE pseudoinstructions
                    assert_eq!(proto.upval_count, 0);
                    vals[a as usize] = LValue::Closure(Closure::from_lua(proto));
                },
                Opcode::CALL => {
                    let (a, b, c) = <CALL as Instruction>::Unpack::unpack(inst.0);
                    dbg!(a, b, c);
                    let to_call = &vals[a as usize];
                    dbg!(to_call);
                    // push where to return to once we RETURN
                    if let LValue::Closure(lcall @ Closure::Lua(_)) = to_call {
                        callstack.push((clos.clone(), pc));
                        clos = lcall.clone();
                        pc = 0;
                    } else if let LValue::Closure(Closure::Native(ncall)) = to_call {
                        let args = if b == 0 {
                            &[]
                        } else {
                            &vals[a as usize+1..=(a as usize + b as usize - 1)]
                        };
                        let ret = (ncall.borrow_mut().native)(args);
                        // FIXME(metatables): __call
                        println!("oh no");
                    }
                    dbg!(to_call);
                },
                Opcode::RETURN => {
                    let (a, b) = <RETURN as Instruction>::Unpack::unpack(inst.0);
                    dbg!(a, b);
                    let r_vals = if b == 1 {
                        // no return values
                        vec![]
                    } else if b >= 2 {
                        // there are b-1 return values from R(A) onwards
                        let r_count = b-1;
                        let r_vals = &vals[a as usize..(a as u16 + r_count) as usize];
                        dbg!(r_vals);
                        Vec::from(r_vals)
                    } else if b == 0 {
                        // return all values from R(A) to the ToS
                        let r_vals = &vals[a as usize..];
                        dbg!(r_vals);
                        Vec::from(r_vals)
                    } else {
                        unreachable!()
                    };
                    if let Some((ret_clos, caller)) = callstack.pop() {
                        clos = ret_clos;
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
