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
    // if typeof(idx) == ty, pc+=1
    Typecheck(Idx, RLRef),
    // if typeof(idx) != ty, pc+=1
    NTypecheck(Idx, RLRef),
    Thunk(ThunkRef),
    Jump(Displacement),
    Ret,
}

struct Vm {
    bytecode: Vec<Operation>,
    in_progress: Option<Vec<Operation>>,
    thunks: Vec<Box<Thunk>>,

    rl_int: RLRef,
}

impl Vm {
    fn new(bytecode: Vec<Operation>) -> Self {
        Self { bytecode, in_progress: None, thunks: vec![],
            rl_int: RLRef(Rc::new(LValue::U32(TypeEq::NEW))),
        }
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
    fn run<'a, const SPEC: bool>(&mut self, mut vals: Vec<RValue<'a>>, mut val_types: Vec<RLRef>) -> Vec<RValue<'a>> {
        let mut pc = 0;
        // We don't know any types initially
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
                                // Don't statically know the type check would succeed,
                                // and need to emit a runtime one.
                                // This is the same as if we unconditionally emitted
                                // a typecheck + two thunks and then immediately
                                // forced one: there's no reason to do that, and
                                // resolving the typecheck immediately allows us
                                // to fastpath the seen type for straightline code.
                                if ty_left.0.compatible(&self.rl_int) {
                                    // Runtime check succeeded, fastpath int
                                    self.in_progress.as_mut().unwrap().push(
                                        Operation::Typecheck(left, self.rl_int.clone()));
                                    self.in_progress.as_mut().unwrap().push(
                                        Operation::Thunk(ThunkRef(Rc::new(RefCell::new(|vm: &mut Vm| {
                                        // failed type check
                                        // TODO; userdata specialization
                                        panic!()
                                    })))));
                                    val_types[left as usize] = ty_left;
                                    // succeeded type check
                                } else {
                                    // Runtime check failed, fastpath other
                                    self.in_progress.as_mut().unwrap().push(
                                        Operation::NTypecheck(left, self.rl_int.clone()));
                                    // TODO: userdata specialization
                                    panic!();
                                }
                            }

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
                    Operation::NTypecheck(idx, ty) => {
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
        if SPEC {
            // we recorded a block up until an exit. finalize the in-progress
            // specialized block, and save it off as a version.
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
    let vals = vec![RValue::Int(0), RValue::Int(1), RValue::Table(Default::default())];
    let mut val_types = vec![RLRef(Rc::new(())); vals.len()];
    dbg!(vm.run::<false>(vals.clone(), val_types.clone()));
    dbg!(vm.run::<true>(vals, val_types));

    dbg!(&vm.in_progress);

    println!("sandbox");
}
