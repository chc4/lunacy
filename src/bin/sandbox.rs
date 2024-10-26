#![feature(trait_alias)]
use typewit::{MakeTypeWitness, TypeEq, HasTypeWitness};
use std::any::TypeId;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::rc::Rc;
use std::cell::{Cell, RefCell};
use std::borrow::Borrow;
use std::collections::BTreeMap;

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
        self.name() == got.0.name()
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

impl PartialEq for RLRef {
    fn eq(&self, other: &Self) -> bool {
        self.0.compatible(other) && other.0.compatible(other)
    }
}

impl Eq for RLRef { }

impl std::hash::Hash for RLRef {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_usize(Rc::as_ptr(&self.0) as *const _ as *const () as usize)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum RValue<'a> {
    Int(u32),
    Str(&'a str),
    Table(BTreeMap<RValue<'a>, RValue<'a>>),
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
        RValue::Str(s) => {
            return add_1(s, right)
        },
        _ => unimplemented!(),
    }
}


fn add_1<'a, 'b, 'c, L: LUnknown<'a>>(left: L, right: RValue<'b>) -> RValue<'c> {
    match right {
        RValue::Int(i) => {
            return add(left, i)
        },
        RValue::Str(s) => {
            return add(left, s)
        },
        _ => unimplemented!(),
    }
}

fn add<'a, 'b, 'c, L: LUnknown<'a>, R: LUnknown<'b>>(left: L, right: R) -> RValue<'c> {
    match (L::WITNESS, R::WITNESS) {
        (LValue::U32(l_te), LValue::U32(r_te)) => {
            RValue::Int(l_te.to_right(left) + r_te.to_right(right))
        },
        (LValue::U32(l_te), LValue::STR(r_te)) => {
            let int_r: u32 = u32::from_str_radix(r_te.to_right(right), 10).unwrap();
            RValue::Int(l_te.to_right(left) + int_r)
        },
        (LValue::STR(l_te), LValue::STR(r_te)) => {
            let int_l: u32 = u32::from_str_radix(l_te.to_right(left), 10).unwrap();
            let int_r: u32 = u32::from_str_radix(r_te.to_right(right), 10).unwrap();
            RValue::Int(int_l + int_r)
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
type Thunk = dyn for<'a> FnMut(&'a mut Vm)->(Pc, Vec<RLRef>, Operation);
#[derive(Clone)]
struct ThunkRef(Rc<RefCell<Thunk>>);
impl std::fmt::Debug for ThunkRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "thunk({:p})", self.0.as_ref() as &_ as *const _ as *const ())
    }
}

impl PartialEq for ThunkRef {
    fn eq(&self, other: &Self) -> bool {
        // just say thunks are never equal to eachother
        false
    }
}

impl ThunkRef {
    fn from(f: impl for<'a> FnMut(&'a mut Vm)->(Pc, Vec<RLRef>, Operation) + 'static) -> Self {
        ThunkRef(Rc::new(RefCell::new(f)))
    }
}

#[derive(Clone, Debug, PartialEq)]
enum Operation {
    Add__(Idx, Idx, Idx),
    AddInt_(Idx, Idx, Idx),
    AddIntInt(Idx, Idx, Idx),
    // if typeof(idx) == ty, pc+=1
    Typecheck(Idx, RLRef),
    // if typeof(idx) != ty, pc+=1
    NTypecheck(Idx, RLRef),
    // if (b == c) != a, pc+=1
    Eq(Idx, Idx, Idx),
    Thunk(ThunkRef),
    Jump(Displacement),
    Nop,
    Ret,
}

type Version = u16;
type Block = u16;
type Pc = usize;
struct Vm {
    bytecode: Vec<Operation>,
    in_progress: Option<Vec<Operation>>,

    // Function PC -> [Types] -> (Block offset)
    versions: HashMap<Pc, HashMap<Vec<RLRef>, Block>>,
    // is there a better way to do it than this? map of version N pc back to version 0
    // pc
    original_pc: HashMap<Pc, Pc>,
    version_count: Version,
    rl_int: RLRef,
    rl_unit: RLRef,
}

impl Vm {
    fn new(bytecode: Vec<Operation>) -> Self {
        let blocks = Self::collect_blocks(&bytecode);
        dbg!(&blocks);
        let vm = Self { bytecode,
            in_progress: None,
            versions: HashMap::from_iter(blocks.iter().map(|pc| (*pc, Default::default()))),
            // Each version 0 pc is its own original pc
            original_pc: HashMap::from_iter(blocks.iter().map(|b| (*b, *b))),
            version_count: 1,
            rl_int: RLRef(Rc::new(LValue::U32(TypeEq::NEW))),
            rl_unit: RLRef(Rc::new(())),
        };

        vm
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
            RValue::Str(s) => RLRef(Rc::new(LValue::STR(TypeEq::NEW))),
            _ => unimplemented!(),
        }
    }

    fn compatible_block(&self, pc: Pc, val_types: &Vec<RLRef>, op: Operation) -> Option<Block> {
        if let Some(versions) = self.versions.get(&(pc as usize)) {
            dbg!(&val_types, &op);
            for (version, block) in versions {
                dbg!(version, &self.bytecode.get(*block as usize));
                if val_types == version && ((self.bytecode.get(*block as usize) == Some(&op)) || op == Operation::Nop) {
                    return Some(*block)
                }
            }
        }
        None
    }

    fn type_guard<'a>(&mut self,
                      pc: Pc,
                      vals: &Vec<RValue<'a>>,
                      val_types: &mut Vec<RLRef>,
                      idx: Idx, ty: RLRef, left: impl Into<ThunkRef>, right: impl Into<ThunkRef>) -> (Option<Pc>, Option<Vec<RLRef>>) {
        // If our type statically already matches, then we can use the right thunk
        // always.
        if val_types[idx as usize].0.compatible(&ty) {
            return (None, Some(val_types.clone()))
        }

        // Dynamic check to see which thunk we'll actually take, and then bias
        // an emitted type guard for that case.
        let runtime_ty = self.typeof_(&vals[idx as usize]);
        if runtime_ty.0.compatible(&ty) {
            // Bias type matches
            let (left_pc, left_ty, left_op) = (left.into().0.borrow_mut())(self);
            dbg!(&left_pc, &left_ty, &left_op);
            if let Some(existing_left) = self.compatible_block(left_pc, &left_ty, left_op) {
                self.in_progress.as_mut().unwrap().push(
                    Operation::Jump(existing_left as i16));
                return (Some(existing_left as Pc), Some(left_ty))
            }
            self.in_progress.as_mut().unwrap().push(
                Operation::Typecheck(idx, ty.clone()));
            self.in_progress.as_mut().unwrap().push(
                Operation::Thunk(right.into()));

            let new_block = self.bytecode.len() + self.in_progress.as_ref().unwrap().len();
            self.versions.entry(pc-1 as usize)
                .or_insert_with(|| HashMap::new())
                .insert(left_ty.clone(), new_block as u16);
            (None, Some(left_ty))
        } else {
            // Bias type fail
            let (right_pc, right_ty, right_op) = (right.into().0.borrow_mut())(self);
            dbg!(&right_pc, &right_ty, &right_op);
            if let Some(existing_right) = self.compatible_block(right_pc, &right_ty, right_op) {
                self.in_progress.as_mut().unwrap().push(
                    Operation::Jump(existing_right as i16));
                return (Some(existing_right as Pc), None)
            }
            self.in_progress.as_mut().unwrap().push(
                Operation::NTypecheck(idx, ty.clone()));
            self.in_progress.as_mut().unwrap().push(
                Operation::Thunk(left.into()));
            let new_block = self.bytecode.len() + self.in_progress.as_ref().unwrap().len();
            self.versions.entry(pc-1 as usize)
                .or_insert_with(|| HashMap::new())
                .insert(val_types.clone(), new_block as u16);
            (None, None)
        }

    }

    // Collect the starting PC of each block in the function.
    // Lua doesn't have dynamic jumps, so we are able to find them with a single
    // traversal and no abstract interpretation.
    fn collect_blocks(bytecode: &Vec<Operation>) -> Vec<Pc> {
        let mut blocks = vec![0];

        for (pc, inst) in bytecode.iter().enumerate() {
            // Give us the same semantics as actual execution: PC points to the next
            // address when "executing"
            let pc = pc + 1;
            match inst {
                Operation::Eq(_a, _b, _c) => {
                    blocks.push(pc);
                    blocks.push(pc+1);
                },
                Operation::Jump(disp) => {
                    blocks.push((pc as isize + *disp as isize) as usize);
                },
                Operation::Typecheck(_idx, _ty) | Operation::NTypecheck(_idx, _ty) => {
                    blocks.push(pc);
                    blocks.push(pc+1);
                },
                Operation::Thunk(_thunk) => {
                    // We should never see a thunk in our initial version
                    unreachable!()
                }
                _ => { },
            }
        }
        blocks
    }

    fn specialize<'a>(&mut self,
        mut vals: Vec<RValue<'a>>,
        parent: Option<Block>) -> (Block, Vec<RValue<'a>>) {
        // TODO: find most compatible version
        let mut val_types = vec![RLRef(Rc::new(())); vals.len()];
        let new_block = self.bytecode.len();
        let values = self.run::<true>(vals, val_types, parent.unwrap_or(0));
        (new_block as u16, values)
    }

    // SPEC is a const time parameter, so that we can write the same interpreter
    // for specializing and executing code. We need non-specialized operations
    // to have concrete implementations both for the case where we exceed the number
    // of versions for a block, in order to prevent exponential blow-up, and also
    // in order because we want to not specialize blocks until we hit a seen threshold
    // (in order to tweak startup JIT tradeoffs).
    fn run<'a, const SPEC: bool>(&mut self,
        mut vals: Vec<RValue<'a>>,
        mut val_types: Vec<RLRef>,
        block: Block) -> Vec<RValue<'a>> {
        let mut pc: Pc = block as usize;
        dbg!(&val_types);
        let mut our_edges: HashMap<Pc, Pc> = Default::default();
        let mut our_base = self.bytecode.len();
        let mut our_version = None;
        if SPEC {
            // we always re-specialize from version 0 of a block
            //assert_eq!(self.original_pc[&pc], pc);
            our_version = Some(self.version_count);
            self.in_progress = Some(vec![]);
            // Map where our block entry will be once we finalize
            our_edges.insert(our_base, pc);
            // emit initial guard for the types we're specializing to
            for (i, val_type) in val_types.clone().iter().enumerate() {
                if val_type.0.compatible(&RLRef(Rc::new(()))) {
                    continue;
                } else {
                    let actual_type = self.typeof_(&vals[i]).clone();
                    //self.type_guard(our_version.unwrap(), pc, &vals, &mut val_types, i as u8, actual_type,
                    //    ThunkRef(Rc::new(RefCell::new(#[inline] |vm: &mut Vm| {
                    //        unreachable!()
                    //    }))),
                    //    ThunkRef(Rc::new(RefCell::new(|vm: &mut Vm| {
                    //        panic!("entry type guard");
                    //    })))
                    //);
                }
            }
            dbg!(&self.in_progress);
        }

        let seal = |vm: &mut Vm, val_types: &mut Vec<RLRef>, our_edges: HashMap<Pc, Pc>| {
            // we recorded a block up until an exit. finalize the in-progress
            // specialized block, and save it off as a version.
            //vm.versions.entry(block as usize).or_insert_with(|| HashMap::new()).insert(val_types.clone(), our_base as u16);
            vm.original_pc.extend(our_edges.clone());
            vm.version_count += 1;
            let finalized = vm.in_progress.take();
            vm.bytecode.append(&mut finalized.unwrap());
        };

        'pc: loop {
            let mut inst = self.bytecode[pc].clone();
            pc += 1;
            println!("{:?}", inst);
            'step: loop {
                match inst {
                    Operation::Add__(ret, left, right) => {
                        if SPEC {
                            let mut typemap = val_types.clone(); typemap[left as usize] = self.rl_int.clone();
                            let fail_types = val_types.clone();
                            match self.type_guard(pc, &vals, &mut val_types, left, self.rl_int.clone(),
                            ThunkRef::from(move |vm: &mut Vm| {
                                (pc-1, typemap.clone(), Operation::AddInt_(ret, left, right)) }),
                            ThunkRef::from(move |vm: &mut Vm| {
                                (pc-1, fail_types.clone(), Operation::Add__(ret, left, right))
                            })) {
                                (None, Some(int_ty)) => {
                                    val_types = int_ty;
                                    inst = Operation::AddInt_(ret, left, right);
                                    continue 'step;
                                },
                                (Some(existing_pc), ty) => {
                                    pc = existing_pc;
                                    ty.map(|ty| val_types = ty );
                                    seal(self, &mut val_types, our_edges);
                                    return self.run::<false>(vals, val_types, pc as Block);
                                },
                                (None, None) => { /* fallthrough */ },
                            }
                            // TODO: specialize userdata
                        }
                        vals[ret as usize] = add_0(vals[left as usize].clone(), vals[right as usize].clone());
                        if SPEC {
                            val_types[ret as usize] = self.rl_int.clone();
                        }
                    },
                    Operation::AddInt_(ret, left, right) => {
                        if SPEC {
                            // Try to specialize on right
                            let mut typemap = val_types.clone(); typemap[right as usize] = self.rl_int.clone();
                            let fail_types = val_types.clone();
                            match self.type_guard(pc, &vals, &mut val_types, right, self.rl_int.clone(),
                            ThunkRef::from(move |vm: &mut Vm| {
                                (pc-1, typemap.clone(), Operation::AddIntInt(ret, left, right)) }),
                            ThunkRef::from(move |vm: &mut Vm| {
                                (pc-1, fail_types.clone(), Operation::AddInt_(ret, left, right))
                            })) {
                                (None, Some(int_ty)) => {
                                    val_types = int_ty;
                                    inst = Operation::AddIntInt(ret, left, right);
                                    continue 'step;
                                },
                                (Some(existing_pc), ty) => {
                                    pc = existing_pc;
                                    ty.map(|ty| val_types = ty );
                                    seal(self, &mut val_types, our_edges);
                                    return self.run::<false>(vals, val_types, pc as Block);
                                },
                                (None, None) => { /* fallthrough */ },
                            }
                            // TODO: specialize userdata
                        }

                        vals[ret as usize] = add_1(
                            unsafe { vals[left as usize].assume_int() },
                            vals[right as usize].clone()
                        );
                        if SPEC {
                            val_types[ret as usize] = self.rl_int.clone();
                        }
                    },
                    Operation::AddIntInt(ret, left, right) => {
                        vals[ret as usize] = add(
                            unsafe { vals[left as usize].assume_int() },
                            unsafe { vals[right as usize].assume_int() },
                        );
                        if SPEC {
                            val_types[ret as usize] = self.rl_int.clone();
                        }
                    },
                    Operation::Typecheck(idx, ref ty) => {
                        if SPEC {
                            panic!();
                        }
                        if self.typeof_(&vals[idx as usize]).0.compatible(&ty) {
                            pc += 1;
                        }
                    },
                    Operation::NTypecheck(idx, ref ty) => {
                        if SPEC {
                            panic!();
                        }
                        if !self.typeof_(&vals[idx as usize]).0.compatible(&ty) {
                            pc += 1;
                        }
                    },
                    Operation::Ret => {
                        if SPEC {
                            // we finished this block
                            //self.in_progress.take();
                            self.in_progress.as_mut().unwrap().push(inst);
                        }
                        break 'pc;
                    },
                    Operation::Jump(bl) => {
                        if SPEC {
                            // If it was an actual jump in our version 0 block,
                            // then we want to specialize into a jump to a specialized
                            // jump target if it already exists.
                            // TODO: we want to finalize our existing block
                            // and switch back to the non-specializing run here,
                            // because we've merged back into existing code

                            if let Some(spec_block) = self.compatible_block(
                                bl as usize, &val_types, self.bytecode[bl as usize].clone())
                            {
                                self.in_progress.as_mut().unwrap().push(
                                    Operation::Jump(spec_block as i16));
                            } else {
                                self.in_progress.as_mut().unwrap().push(
                                    Operation::Jump(bl));
                            }
                        }
                        pc = bl as usize;
                        continue 'pc;
                    },
                    Operation::Eq(a, b, c) => {

                        let mut taken = false;
                        if RValue::Int((vals[b as usize] == vals[c as usize]) as u32)
                            != vals[a as usize]
                        {
                            taken = true;
                            pc += 1;
                        }
                        if SPEC {
                            // Block exit: we do the same thing as type specialization
                            // in that we can produce and force thunks, biased to
                            // straightline code, but we have to record either side
                            // as a block version if it was already externally
                            // visible: if we have code that branches A -> B -> {C, _} -> B
                            // we want A' -> B' -> C' to jump back to our existing
                            // B' instead of the original.
                            // We could do an initial pass when we load version 0
                            // where we only produce "blocks" for code transitively
                            // reachable from jump targets with >1 incoming edges
                            // I think...?
                            // Alternatively, we could process EQ+JMP together and
                            // avoid needing to emit a thunk entirely.
                            dbg!(block);
                            // EQ is always formatted like EQ+JMP false+true. We want
                            // to turn it into either EQ+false thunk+true or NEQ+true thunk+false,
                            // because we want to emit a thunk to lazily process the
                            // target we aren't taking.
                            if taken {
                                // Emit a thunk for the JMP false
                                self.in_progress.as_mut().unwrap().push(Operation::Eq(a, b, c));
                                // Record the EQ jump target location
                                self.in_progress.as_mut().unwrap().push(Operation::Thunk(
                                    ThunkRef(Rc::new(RefCell::new(|vm: &mut Vm| {
                                        panic!("taken false thunk");
                                    }))))
                                );
                                // Record the EQ fallthrough jump location
                                our_edges.insert(our_base+self.in_progress.as_ref().unwrap().len(), pc+1);
                                break 'step;
                            } else {
                                panic!()
                            }
                        }
                    },
                    Operation::Thunk(ref thunk) => {
                        let (new_pc, new_types, op) = (thunk.0.borrow_mut())(self);
                        dbg!(&new_pc, &new_types, &op);
                        if let Some(existing) = self.compatible_block(new_pc, &new_types, op) {
                            println!("compatible block for thunk");
                            self.bytecode[pc as usize - 1] = Operation::Jump(existing as i16);
                            pc = existing as usize;
                            continue 'pc;
                        }
                        if SPEC {
                            panic!("thunk when specializing");
                        }
                        // Specialize a new block and rewrite thunk into a jump
                        self.bytecode[pc as usize - 1] = Operation::Jump(self.bytecode.len() as i16);
                        return self.run::<true>(vals, new_types, new_pc as u16);
                    },
                    Operation::Nop => {
                        println!("hit nop")
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
            seal(self, &mut val_types, our_edges);
        }
        return vals
    }
}

fn main() {
    dbg!(add_0(RValue::Int(1), RValue::Int(2)));

    let bytecode = vec![
        Operation::Add__(0, 0, 1),
        Operation::Add__(0, 0, 1),
        Operation::Eq(0, 0, 0),
        Operation::Nop,
        Operation::Ret
    ];

    let mut vm = Vm::new(bytecode);
    let vals_int_int = vec![RValue::Int(0), RValue::Int(1)];
    let vals_int_str = vec![RValue::Int(1), RValue::Str("2")];
    let vals_str_str = vec![RValue::Str("1"), RValue::Str("2")];
    let vals_str_int = vec![RValue::Str("1"), RValue::Str("2")];
    let mut val_types = vec![RLRef(Rc::new(())); vals_int_int.len()];
    dbg!(vm.run::<false>(vals_int_int.clone(), val_types.clone(), 0));
    let (v1, _) = vm.specialize(vals_int_int.clone(), None);
    let (v2, _) = vm.specialize(vals_int_str.clone(), None);
    let (v3, _) = vm.specialize(vals_str_str.clone(), None);

    dbg!(vm.run::<false>(vals_int_int.clone(), val_types.clone(), v1));
    dbg!(vm.run::<false>(vals_int_str.clone(), val_types.clone(), v1));
    dbg!(vm.run::<false>(vals_str_str.clone(), val_types.clone(), v1));
    dbg!(vm.run::<false>(vals_str_int.clone(), val_types.clone(), v1));

    dbg!(vm.run::<false>(vals_int_int.clone(), val_types.clone(), v3));
    dbg!(vm.run::<false>(vals_int_str.clone(), val_types.clone(), v3));
    dbg!(vm.run::<false>(vals_str_str.clone(), val_types.clone(), v3));
    dbg!(vm.run::<false>(vals_str_int.clone(), val_types.clone(), v3));

    let entry_int_int = vm.compatible_block(0, &vec![vm.rl_int.clone(); 2], Operation::Nop).unwrap();
    dbg!(vm.run::<false>(vals_int_int.clone(), val_types.clone(), entry_int_int));

    //dbg!(vm.run::<false>(vec![RValue::Int(1), RValue::Str("test")], val_types.clone(), Some(1)));

    dbg!(&vm.bytecode);

    println!("sandbox");
}
