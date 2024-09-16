use crate::chunk::FunctionBlock;
use core::hash::Hash;
use std::{error::Error, rc::Rc};
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


#[derive(Debug)]
struct Gc<T>(Rc<T>);

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
        Self(Rc::new(val))
    }
}

impl<T> Clone for Gc<T> {
    fn clone(&self) -> Self {
        Gc(self.0.clone())
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum LValue<'lua, 'src> {
    Nil,
    Bool(bool),
    Number(Number),
    String(String),
    Closure(Gc<Closure<'lua, 'src>>),
    //Table(Table),
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
struct Closure<'lua, 'src> {
    prototype: &'lua FunctionBlock<'src>,
    //environment: LTable<'src>,
    //upvalues: Vec<Upvalue<'lua>>,
}

impl<'lua, 'src> Closure<'lua, 'src> {
    fn new(prototype: &'lua FunctionBlock<'src>) -> Self {
        Self {
            prototype
        }
    }
}

pub struct Vm<'src> {
    top_level: FunctionBlock<'src>
}

impl<'src> Vm<'src> {
    pub fn new(top_level: FunctionBlock<'src>) -> Self {
        Self { top_level }
    }

    pub fn run<'a>(&'a mut self) -> Result<Vec<LValue<'a, 'src>>, Box<dyn Error>> {
        // we should create a new closure for the top_level and run that instead
        let clos = &self.top_level;
        let mut vals: Vec<LValue> = vec![LValue::from(Constant::Nil); clos.max_stack as usize];
        let mut globals = std::collections::HashMap::<LValue, LValue>::new();
        let r_vals = 'int: { for inst in &self.top_level.instructions.items {
            println!("inst {:?}", inst.0.Opcode());
            match inst.0.Opcode() {
                Opcode::MOVE => {
                    let (a, b) = <MOVE as Instruction>::Unpack::unpack(inst.0);
                    dbg!(a, b);
                    vals[a as usize] = vals[b as usize].clone();
                },
                Opcode::LOADK => {
                    let (a, bx) = <LOADK as Instruction>::Unpack::unpack(inst.0);
                    dbg!(a, bx, &clos.constants.items[bx as usize]);
                    vals[a as usize] = clos.constants.items[bx as usize].clone().into();
                    ()
                },
                Opcode::SETGLOBAL => {
                    let (a, bx) = <SETGLOBAL as Instruction>::Unpack::unpack(inst.0);
                    let kst = &clos.constants.items[bx as usize];
                    dbg!(a, bx, &kst);
                    globals.insert(kst.clone().into(), vals[a as usize].clone());
                },
                Opcode::GETGLOBAL => {
                    let (a, bx) = <SETGLOBAL as Instruction>::Unpack::unpack(inst.0);
                    let kst = &clos.constants.items[bx as usize];
                    dbg!(a, bx, &kst);
                    // FIXME(error handling)
                    vals[a as usize] = globals.get(&kst.clone().into()).unwrap_or(&Constant::Nil.into()).clone();
                },
                Opcode::CLOSURE => {
                    let (a, bx) = <CLOSURE as Instruction>::Unpack::unpack(inst.0);
                    let proto = &clos.prototypes.items[bx as usize];
                    dbg!(a, bx, proto);
                    vals[a as usize] = LValue::Closure(Gc::new(Closure::new(proto)));
                },
                Opcode::CALL => {
                    let (a, b, c) = <CALL as Instruction>::Unpack::unpack(inst.0);
                    dbg!(a, b, c);
                    let to_call = &vals[a as usize];
                    dbg!(to_call);
                },
                Opcode::RETURN => {
                    let (a, b) = <RETURN as Instruction>::Unpack::unpack(inst.0);
                    dbg!(a, b);
                    if b == 1 {
                        // no return values
                        break 'int vec![];
                    } else if b >= 2 {
                        // there are b-1 return values from R(A) onwards
                        let r_count = b-1;
                        let r_vals = &vals[a as usize..(a as u16 + r_count - 1) as usize];
                        dbg!(r_vals);
                        break 'int Vec::from(r_vals);
                    } else if b == 0 {
                        // return all values from R(A) to the ToS
                        let r_vals = &vals[a as usize..];
                        dbg!(r_vals);
                        break 'int Vec::from(r_vals);
                    }
                },
                Opcode::INVALID => unreachable!(),
                x => unimplemented!("opcode {:?}", x),
                _ => (),
            }
        } vec![] };
        Ok(r_vals)
    }
}
