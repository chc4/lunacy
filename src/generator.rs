#![allow(unused_variables)]

use std::collections::HashMap;
use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;
use std::rc::Rc;
use std::cell::RefCell;

use crate::vm::Opcode;
use qcell::{TCell, TCellOwner};
use crate::vm::{Tc, TcOwner};
use crate::vm::LClosure;
use crate::vm::{LValue, LType, Number};
use crate::chunk::Instruction;

use log::debug;

fn typeof_<'src, 'intern>(val: &LValue<'src, 'intern>) -> LType {
    match val {
        LValue::Number(_) => LType::Number,
        LValue::InternedString(_) | LValue::OwnedString(_) => LType::String,
        _ => LType::Unknown,
    }
}

#[derive(Clone)]
struct ResidualExec(&'static str, Rc<dyn for <'src, 'intern> Fn(&mut [LValue<'src, 'intern>])>);
impl std::fmt::Debug for ResidualExec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "exec({}, {:p})", self.0, self.1.as_ref() as &_ as *const _ as *const ())
    }
}

#[derive(Clone)]
pub enum YieldOp {
    Guard(usize, LType),
    Exec(ResidualExec),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ResumeArg {
    Start,
    Matched,
    Failed,
}

pub fn emit_add(dest: usize, lhs: usize, rhs: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = Vec<(usize, LType)>> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        // --- Int Path ---
        arg = yield YieldOp::Guard(lhs, LType::Number);
        if arg == ResumeArg::Matched {
            arg = yield YieldOp::Guard(rhs, LType::Number);
            if arg == ResumeArg::Matched {
                // TODO: is_constant for kb/kc? yeah that's needed for constant type effects
                yield YieldOp::Exec(ResidualExec("add_int_int", Rc::new(move |vals| {
                    // Safe bypass of runtime checks
                    let LValue::Number(Number(l)) = vals[lhs] else { unreachable!() };
                    let LValue::Number(Number(r)) = vals[rhs] else { unreachable!() };
                    vals[dest] = LValue::Number(Number(l + r));
                })));
                return vec![(dest, LType::Number)];
            }
        }

        // --- Str Path ---
        arg = yield YieldOp::Guard(lhs, LType::String);
        if arg == ResumeArg::Matched {
            arg = yield YieldOp::Guard(rhs, LType::String);
            if arg == ResumeArg::Matched {
                yield YieldOp::Exec(ResidualExec("add_str_str", Rc::new(move |vals| {
                    //let RValue::Str(l) = &vals[lhs] else { unreachable!() };
                    //let RValue::Str(r) = &vals[rhs] else { unreachable!() };
                    //vals[dest] = RValue::Str(l.clone() + r);
                    unimplemented!()
                })));
                return vec![(dest, LType::String)];
            }
        }

        // --- Generic/Trap Fallback ---
        panic!("Type mismatch trap");
    }
}

pub fn emit_move(dest: usize, src: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = Vec<(usize, LType)>> + Clone + Unpin {
    #[coroutine]
    move |arg: ResumeArg| {
        yield YieldOp::Exec(ResidualExec("move", Rc::new(move |vals| {
            vals[dest] = vals[src].clone();
        })));
        // TODO: track references? see PyLBBV
        return vec![(dest, LType::Unknown)];
    }
}


type BlockId = usize;
type Pc = usize;
#[derive(PartialEq, Eq, Clone, Copy, Hash, Debug)]
struct SubPc(usize, usize);

impl SubPc {
    fn new(pc: Pc) -> Self {
        SubPc(pc, 1)
    }
    fn next_pc(&self) -> Self {
        Self::new(self.0 + 1)
    }
    fn next_true(&self) -> Self {
        assert!(self.1 < (1<<32));
        Self(self.0, (self.1 << 1) | 1)
    }
    fn next_false(&self) -> Self {
        assert!(self.1 < (1<<32));
        Self(self.0, self.1 << 1)
    }
}

#[derive(Clone)]
pub struct ThunkRef(pub Rc<RefCell<dyn FnMut(&mut Specializer, &TCellOwner<TcOwner>) -> ()>>);

impl std::fmt::Debug for ThunkRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "Thunk(...)") }
}

#[derive(Debug, Clone)]
pub enum Residual {
    Guard { idx: usize, expected: LType },
    Exec(ResidualExec),
    Jump(BlockId),
    Thunk(ThunkRef),
    Ret,
}

pub struct Specializer<'src, 'intern> {
    pub clos: Tc<LClosure<'src, 'intern>>,
    pub blocks: Vec<Vec<Residual>>,
    pub versions: HashMap<(SubPc, Vec<LType>), BlockId>,
}

impl<'src, 'intern> Specializer<'src, 'intern> {
    pub fn new(clos: Tc<LClosure<'src, 'intern>>) -> Self {
        Self {
            clos,
            blocks: Vec::new(),
            versions: Default::default(),
        }
    }

    pub fn block(&mut self, owner: &TCellOwner<TcOwner>, entry: Pc, types: Vec<LType>) -> BlockId {
        let mut pc = entry;

        let block_id = self.new_block();
        let subpc: SubPc = SubPc::new(entry);
        self.versions.insert((subpc, types.clone()), block_id);
        self.compile(owner, entry, types, block_id);
        return block_id;
    }

    fn code<'a>(&self,
        owner: &'a TCellOwner<TcOwner>,
        pc: Pc) -> &'a Instruction
        where 'intern: 'a
    {
        let inst = unsafe { &self.clos.ro(owner).prototype.as_ref().unwrap().instructions.items[pc] };
        return inst;
    }

    pub fn compile(&mut self, owner: &TCellOwner<TcOwner>, mut pc: Pc, mut types: Vec<LType>, block_id: usize) -> Vec<LType> {
        loop {
            debug!("compile {pc}");
            let instruction = self.code(owner, pc).clone();
            if let Some((next, ty)) = match instruction.0.Opcode() {
                Opcode::ADD => { panic!() },
                //Operation::Add(o, l, r) => self.compile_one(SubPc::new(pc), types.clone(), emit_add(o, l, r), ResumeArg::Start, block_id),
                //Operation::Ret => {
                //    println!("ret");
                //    self.blocks[block_id].push(Residual::Ret); None
                //},
                _ => panic!()
            } {
                pc = next;
                types = ty;
                println!("-> {}", next);
            } else {
                return types;
            }
        }
    }

    pub fn new_block(&mut self) -> BlockId {
        self.blocks.push(Vec::new());
        self.blocks.len() - 1
    }

    pub fn compile_one<C>(&mut self, mut pc: SubPc, mut types: Vec<LType>, mut coro: C, mut arg: ResumeArg, block_id: usize) -> Option<(Pc, Vec<LType>)>
    where
        C: Coroutine<ResumeArg, Yield = YieldOp, Return = Vec<(usize, LType)>> + Clone + Unpin + 'static,
    {
        loop {
            match Pin::new(&mut coro).resume(arg) {
                CoroutineState::Yielded(YieldOp::Guard(idx, expected)) => {
                    if types[idx] == expected {
                        // Statically true: pump the success path
                        pc = pc.next_true();
                        arg = ResumeArg::Matched;
                    } else if types[idx] != LType::Unknown {
                        // Statically false: pump the fail path
                        pc = pc.next_false();
                        arg = ResumeArg::Failed;
                    } else {
                        // Dynamic branch: Fork the coroutine
                        let fail_coro = coro.clone();
                        let fail_types = types.clone();
                        let fail_off = self.blocks[block_id].len() + 1;
                        self.blocks[block_id].push(Residual::Guard { idx, expected: expected.clone() });

                        self.blocks[block_id].push(Residual::Thunk(ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &TCellOwner<TcOwner>| {
                            let fail_pc = pc.next_false();
                            dbg!(fail_off);
                            // This executes only if the dynamic branch fails at runtime
                            println!("before compile_one");
                            // See if the block already exists
                            if let Some(exists) = vm.versions.get(&(fail_pc, fail_types.clone())) {
                                dbg!("fail exists {exists}");
                                vm.blocks[block_id][fail_off] = Residual::Jump(*exists);
                                return;
                            }
                            let fail_thunk_id = vm.new_block();
                            if let Some((fail_next, fail_ty)) = vm.compile_one(fail_pc, fail_types.clone(), fail_coro.clone(), ResumeArg::Failed, fail_thunk_id) {
                                // We finished running the coroutine to completion, finish the
                                // rest of the block
                                vm.compile(owner, fail_next, fail_ty, fail_thunk_id);
                            } else {
                                // The coroutine got stuck on another thunk
                            }
                            // Patch the thunk block to jump to the newly specialized block
                            vm.versions.insert((fail_pc, fail_types.clone()), fail_thunk_id);
                            vm.blocks[block_id][fail_off] = Residual::Jump(fail_thunk_id);
                        })))));
                        let succ_coro = coro.clone();
                        let succ_off = fail_off + 1;
                        self.blocks[block_id].push(Residual::Thunk(ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &TCellOwner<TcOwner>| {
                            let succ_pc = pc.next_true();
                            dbg!(succ_off);
                            // This executes only if the dynamic branch succeeds at runtime
                            let mut success_types = types.clone();
                            success_types[idx] = expected.clone();
                            dbg!("before succ compile_one");
                            // See if the block already exists
                            if let Some(exists) = vm.versions.get(&(succ_pc, success_types.clone())) {
                                dbg!("succ exists {exists}");
                                vm.blocks[block_id][succ_off] = Residual::Jump(*exists);
                                return;
                            }
                            let succ_thunk_id = vm.new_block();
                            if let Some((succ_next, succ_ty)) = vm.compile_one(succ_pc, success_types.clone(), succ_coro.clone(), ResumeArg::Matched, succ_thunk_id) {
                                vm.compile(owner, succ_next, succ_ty, succ_thunk_id);
                            }
                            // Patch the thunk block to jump to the newly specialized block
                            vm.versions.insert((succ_pc, success_types.clone()), succ_thunk_id);
                            vm.blocks[block_id][succ_off] = Residual::Jump(succ_thunk_id);
                        })))));
                        return None;
                    }
                }
                CoroutineState::Yielded(YieldOp::Exec(func)) => {
                    self.blocks[block_id].push(Residual::Exec(func));
                    // In a real VM, transition to the next PC generator here.
                }
                CoroutineState::Complete(ty_effects) => {
                    for (idx, ty) in ty_effects {
                        if idx > types.len() {
                            types.resize(idx + 1, LType::Unknown);
                        }
                        types[idx] = ty;
                    }
                    return Some((pc.0 + 1, types));
                }
            }
        }
    }

    pub fn run(&mut self, owner: &TCellOwner<TcOwner>, mut id: BlockId, mut values: Vec<LValue<'src, 'intern>>) -> Vec<LValue<'src, 'intern>> {
        let mut off = 0;
        loop {
            let block = &self.blocks[id];
            let res = block[off].clone();
            dbg!(&res);
            match res {
                Residual::Guard { idx, expected } => {
                    if typeof_(&values[idx]) == expected {
                        // Fallthrough
                        off += 2;
                    } else {
                        off += 1;
                    }
                },
                Residual::Exec(f) => {
                    f.1(&mut values[..]);
                    off += 1;
                },
                Residual::Jump(target) => {
                    id = target;
                    off = 0;
                },
                Residual::Thunk(thunk) => {
                    dbg!(&block);
                    (thunk.0.borrow_mut())(self, owner)
                },
                Residual::Ret => { return values; },
            }
        }
    }
}

#[cfg(feature="generator")]
fn main() {
    let mut vm = Specializer { code, blocks: vec![], versions: HashMap::new() };

    let dyn_types = vec![LType::Unknown, LType::Unknown, LType::Unknown];
    let dyn_block = vm.block(0, dyn_types);
    println!("{:?}", vm.blocks[dyn_block]);

    let res = vm.run(dyn_block, vec![RValue::Int(0), RValue::Int(1), RValue::Int(2)]);
    dbg!(res);
    let res = vm.run(dyn_block, vec![RValue::Int(0), RValue::Str("1".into()), RValue::Str("2".into())]);
    dbg!(res);
    let res = vm.run(dyn_block, vec![RValue::Str("0".into()), RValue::Int(1), RValue::Int(2)]);
    dbg!(res);

    println!("{:?} blocks:{} instructions:{}", &vm.blocks,
        vm.blocks.len(),
        vm.blocks.iter().fold(0, |i, b| i + b.len()));

    let mut versions = vm.versions.iter().collect::<Vec<_>>();
    versions.sort_by_key(|(subpc, ty)| subpc.0.0);
    println!("versions {:?}", versions);
}
