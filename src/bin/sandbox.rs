#![feature(trait_alias)]
use typewit::{MakeTypeWitness, TypeEq, HasTypeWitness};
use std::any::TypeId;
use std::collections::HashMap;
use std::rc::Rc;
use std::cell::RefCell;
use std::borrow::Borrow;

struct Userdata {
    add: fn(Self)->Self,
}

typewit::simple_type_witness! {
    #[derive(Debug)]
    enum LValue<'a> {
        U32 = u32,
        STR = &'a str,
        USER = Userdata,
    }
}

trait RLValue {
    fn name(&self) -> &'static str {
        std::any::type_name::<Self>()
    }

    fn compatible(&self, got: &RLRef) -> bool;
}

// Unknown type
impl RLValue for () {
    fn compatible(&self, got: &RLRef) -> bool {
        // no type information, always need to emit a check
        false
    }
}
// Static type
impl<'a, T> RLValue for LValue<'a, T> {
    fn compatible(&self, got: &RLRef) -> bool {
        self.name() == got.0.name()
    }
}

impl<'a> std::fmt::Debug for dyn RLValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

#[derive(Debug)]
struct RLRef(Rc<dyn RLValue>);
impl Clone for RLRef {
    fn clone(&self) -> Self {
        RLRef(self.0.clone())
    }
}

#[derive(Debug, Clone)]
enum RValue<'a> {
    Int(u32),
    Str(&'a str),
    Table(HashMap<RValue<'a>, RValue<'a>>),
}

impl<'a> RValue<'a> {
    #[inline]
    unsafe fn assume_int(&self) -> u32 {
        match self {
            RValue::Int(i) => *i,
            _ => panic!(),
        }
    }
}

trait LUnknown<'a> = Clone + HasTypeWitness<LValue<'a, Self>>;

fn increment<'a, V: LUnknown<'a>>(val: V) -> V {
    match V::WITNESS {
        LValue::U32(te) => {
            println!("int {:?}", te.to_right(val.clone()));
            return te.to_left(te.to_right(val) + 1);
        },
        LValue::USER(te) => {
            panic!()
        },
        LValue::STR(te) => {
            panic!()
        },
    }
}

fn add_0<'a, 'b, 'c>(left: RValue<'a>, right: RValue<'b>) -> RValue<'c> {
    match left {
        RValue::Int(i) => {
            return add_1(i, right)
        },
        _ => unimplemented!(),
    }
}


fn add_1<'a, 'b, 'c, L: LUnknown<'a>>(left: L, right: RValue<'b>) -> RValue<'c> {
    match right {
        RValue::Int(i) => {
            return add(left, i)
        },
        _ => unimplemented!(),
    }
}

fn add<'a, 'b, 'c, L: LUnknown<'a>, R: LUnknown<'b>>(left: L, right: R) -> RValue<'c> {
    match (L::WITNESS, R::WITNESS) {
        (LValue::U32(l_te), LValue::U32(r_te)) => {
            RValue::Int(l_te.to_right(left) + r_te.to_right(right))
        },
        _ => unimplemented!(),
    }
}

fn increment_r<'a>(rval: RValue<'a>) -> RValue<'a> {
    match rval {
        RValue::Int(i) => RValue::Int(increment(i)),
        RValue::Str(s) => panic!(),
        RValue::Table(t) => panic!(),
    }
}

type Idx = u8;
type Displacement = i16;
type Thunk = dyn for<'a> FnMut(&'a mut Vm);
#[derive(Clone)]
struct ThunkRef(Rc<RefCell<Thunk>>);
impl std::fmt::Debug for ThunkRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "thunk({:p})", self.0.as_ref() as &_ as *const _ as *const ())
    }
}
#[derive(Clone, Debug)]
enum Operation {
    Add__(Idx, Idx, Idx),
    AddInt_(Idx, Idx, Idx),
    AddIntInt(Idx, Idx, Idx),
    Typecheck(Idx, RLRef),
    Thunk(ThunkRef),
    Jump(Displacement),
    Ret,
}

struct Vm {
    bytecode: Vec<Operation>,
    in_progress: Option<Vec<Operation>>,
    thunks: Vec<Box<Thunk>>,
}

impl Vm {
    fn new(bytecode: Vec<Operation>) -> Self {
        Self { bytecode, in_progress: None, thunks: vec![] }
    }

    fn infer<'a, 'b>(&mut self, vals: Vec<RValue<'a>>) -> Vec<Box<dyn RLValue + 'static>> {
        vals.iter().map(|v| {
            match v {
                RValue::Int(i) => Box::new(LValue::U32(TypeEq::NEW)) as Box<_>,
                RValue::Table(t) => Box::new(LValue::USER(TypeEq::NEW)) as Box<_>,
                _ => panic!(),
            }
        }).collect()
    }

    fn typeof_<'a>(&mut self, val: &RValue<'a>) -> RLRef {
        match val {
            RValue::Int(i) => RLRef(Rc::new(LValue::U32(TypeEq::NEW))),
            _ => unimplemented!(),
        }
    }

    fn specialize(&mut self, idx: Idx, ty: RLRef, left: Box<Thunk>, right: Box<Thunk>) {
        self.thunks.push(left);
        self.thunks.push(right);
    }

    // SPEC is a const time parameter, so that we can write the same interpreter
    // for specializing and executing code. We need non-specialized operations
    // to have concrete implementations both for the case where we exceed the number
    // of versions for a block, in order to prevent exponential blow-up, and also
    // in order because we want to not specialize blocks until we hit a seen threshold
    // (in order to tweak startup JIT tradeoffs).
    fn run<'a, const SPEC: bool>(&mut self, mut vals: Vec<RValue<'a>>) -> Vec<RValue<'a>> {
        let mut pc = 0;
        // We don't know any types initially
        let mut val_types = vec![RLRef(Rc::new(())); vals.len()];
        dbg!(&val_types);
        if SPEC {
            self.in_progress = Some(vec![]);
        }
        'pc: loop {
            let mut inst = self.bytecode[pc].clone();
            pc += 1;
            'step: loop {
                match inst {
                    Operation::Add__(ret, left, right) => {
                        if SPEC {
                            // Try to specialize on left
                            let ty_left = self.typeof_(&vals[left as usize]);
                            if !val_types[left as usize].0.compatible(&ty_left) {
                                dbg!(&ty_left);
                                self.in_progress.as_mut().unwrap().push(
                                    Operation::Typecheck(left, ty_left.clone()));
                                self.in_progress.as_mut().unwrap().push(
                                    Operation::Thunk(ThunkRef(Rc::new(RefCell::new(|vm: &mut Vm| {
                                    // failed type check
                                    // emit run::<SPEC=true>(pc) to specialize the block again, and patch
                                    // this thunk with a jump to the new block. this means that we'd
                                    // specialize for each new type we see immediately: we know the
                                    // non-thunk block is hot enough to specialize, and don't record number
                                    // of times we see a type, so there's limited reason to try and delay
                                    // specializing again.
                                    panic!()
                                })))));
                            }
                            // succeeded type check
                            // continue execution with AddInt_ since we know the type
                            val_types[left as usize] = ty_left;
                            inst = Operation::AddInt_(ret, left, right);
                            continue 'step;
                        }
                        vals[ret as usize] = add_0(vals[left as usize].clone(), vals[right as usize].clone());
                    },
                    Operation::AddInt_(ret, left, right) => {
                        vals[ret as usize] = add_1(
                            unsafe { vals[left as usize].assume_int() },
                            vals[right as usize].clone()
                        );
                    },
                    Operation::AddIntInt(ret, left, right) => {
                        vals[ret as usize] = add(
                            unsafe { vals[left as usize].assume_int() },
                            unsafe { vals[right as usize].assume_int() },
                        );
                    },
                    Operation::Typecheck(idx, ty) => {
                        panic!()
                    },
                    Operation::Ret => {
                        if SPEC {
                            // we finished this block and there wasn't anything
                            // to specialize. replace the hotcount profiler with
                            // a no-op, so we don't attempt to specialize again
                            // in the future, and then throw away our recorded
                            // in-progress block
                            // TODO: hotcount
                            //self.in_progress.take();
                        }
                        break 'pc;
                    },
                    Operation::Jump(bl) => {
                        panic!()
                    },
                    Operation::Thunk(ref thunk) => {
                        (thunk.0.borrow_mut())(self);
                    },
                }
                if SPEC {
                    // When specializing we record each instruction we executed, but
                    // want to do it *after* so that if we hit a specializable instruction,
                    // it can instead record a type guard 
                    self.in_progress.as_mut().unwrap().push(inst);
                }
                break 'step;
            }
        }
        return vals
    }
}

fn main() {
    dbg!(add_0(RValue::Int(1), RValue::Int(2)));

    let bytecode = vec![
        Operation::Add__(0, 0, 1),
        Operation::Add__(0, 0, 1),
        Operation::Ret
    ];

    let mut vm = Vm::new(bytecode);
    dbg!(vm.run::<false>(vec![RValue::Int(0), RValue::Int(1), RValue::Table(Default::default())]));
    dbg!(vm.run::<true>(vec![RValue::Int(0), RValue::Int(1), RValue::Table(Default::default())]));

    dbg!(&vm.in_progress);

    println!("sandbox");
}
