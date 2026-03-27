#![feature(coroutines, coroutine_trait, coroutine_clone, stmt_expr_attributes)]

use std::collections::HashMap;
use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;
use std::rc::Rc;
use std::cell::RefCell;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty { Int, Str, Unknown }

#[derive(Clone, Debug)]
pub enum RValue { Int(u32), Str(String) }

fn typeof_<'a>(val: &RValue) -> Ty {
    match val {
        RValue::Int(i) => Ty::Int,
        RValue::Str(s) => Ty::Str,
        _ => unimplemented!(),
    }
}

#[derive(Clone)]
struct ResidualExec(Rc<dyn Fn(&mut [RValue])>);
impl std::fmt::Debug for ResidualExec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "exec({:p})", self.0.as_ref() as &_ as *const _ as *const ())
    }
}

#[derive(Clone)]
pub enum YieldOp {
    Guard(usize, Ty),
    Exec(ResidualExec),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ResumeArg {
    Start,
    Matched,
    Failed,
}

// 1. Linearized Generator using Coroutines
pub fn emit_add(dest: usize, lhs: usize, rhs: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ()> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        // --- Int Path ---
        arg = yield YieldOp::Guard(lhs, Ty::Int);
        if arg == ResumeArg::Matched {
            arg = yield YieldOp::Guard(rhs, Ty::Int);
            if arg == ResumeArg::Matched {
                yield YieldOp::Exec(ResidualExec(Rc::new(move |vals| {
                    // Safe bypass of runtime checks
                    let RValue::Int(l) = vals[lhs] else { unreachable!() };
                    let RValue::Int(r) = vals[rhs] else { unreachable!() };
                    vals[dest] = RValue::Int(l + r);
                })));
                return;
            }
        }

        // --- Str Path (Fallback) ---
        arg = yield YieldOp::Guard(lhs, Ty::Str);
        if arg == ResumeArg::Matched {
            arg = yield YieldOp::Guard(rhs, Ty::Str);
            if arg == ResumeArg::Matched {
                yield YieldOp::Exec(ResidualExec(Rc::new(move |vals| {
                    let RValue::Str(l) = &vals[lhs] else { unreachable!() };
                    let RValue::Str(r) = &vals[rhs] else { unreachable!() };
                    vals[dest] = RValue::Str(l.clone() + r);
                })));
                return;
            }
        }

        // --- Generic/Trap Fallback ---
        panic!("Type mismatch trap");
    }
}

// 2. LBBV Compiler/Poller
type BlockId = usize;
type Pc = usize;

#[derive(Debug, Clone)]
pub enum Operation {
    Add(usize, usize, usize),
    Ret
}

#[derive(Clone)]
pub struct ThunkRef(pub Rc<RefCell<dyn FnMut(&mut Vm) -> ()>>);

impl std::fmt::Debug for ThunkRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "Thunk(...)") }
}

#[derive(Debug, Clone)]
pub enum Residual {
    Guard { idx: usize, expected: Ty, fail_target: BlockId },
    Exec(ResidualExec),
    Jump(BlockId),
    Thunk(ThunkRef),
    Ret,
}

pub struct Vm {
    pub code: Vec<Operation>,
    pub blocks: Vec<Vec<Residual>>,
    pub versions: HashMap<(Pc, Vec<Ty>), BlockId>,
}

impl Vm {
    pub fn block(&mut self, entry: Pc, types: Vec<Ty>) -> BlockId {
        let mut pc = entry;

        let block_id = self.new_block();
        self.versions.insert((pc, types.clone()), block_id);

        loop {
            let instruction = self.code[pc].clone();
            if let Some(next) = match instruction {
                Operation::Add(o, l, r) => self.compile(pc, types.clone(), emit_add(o, l, r), ResumeArg::Start, block_id),
                Operation::Ret => None,
            } {
                pc = next;
            } else {
                return block_id;
            }
        }
    }

    pub fn new_block(&mut self) -> BlockId {
        self.blocks.push(Vec::new());
        self.blocks.len() - 1
    }

    pub fn compile<C>(&mut self, orig_pc: Pc, types: Vec<Ty>, mut coro: C, mut arg: ResumeArg, block_id: usize) -> Option<usize>
    where
        C: Coroutine<ResumeArg, Yield = YieldOp, Return = ()> + Clone + Unpin + 'static,
    {
        loop {
            match Pin::new(&mut coro).resume(arg) {
                CoroutineState::Yielded(YieldOp::Guard(idx, expected)) => {
                    if types[idx] == expected {
                        // Statically true: pump the success path
                        arg = ResumeArg::Matched;
                    } else if types[idx] != Ty::Unknown {
                        // Statically false: pump the fail path
                        arg = ResumeArg::Failed;
                    } else {
                        // Dynamic branch: Fork the coroutine
                        let fail_coro = coro.clone();
                        let fail_types = types.clone();
                        let fail_pc = self.blocks[block_id].len() + 1;
                        self.blocks[block_id].push(Residual::Guard { idx, expected: expected.clone(), fail_target: fail_pc });

                        self.blocks[block_id].push(Residual::Thunk(ThunkRef(Rc::new(RefCell::new(move |vm: &mut Vm| {
                            dbg!(fail_pc);
                            // This executes only if the dynamic branch fails at runtime
                            let fail_thunk_id = vm.new_block();
                            vm.compile(orig_pc + 1, fail_types.clone(), fail_coro.clone(), ResumeArg::Failed, fail_thunk_id);
                            // Patch the thunk block to jump to the newly specialized block
                            vm.blocks[block_id][fail_pc] = Residual::Jump(fail_thunk_id);
                        })))));
                        let succ_coro = coro.clone();
                        let succ_pc = fail_pc + 1;
                        self.blocks[block_id].push(Residual::Thunk(ThunkRef(Rc::new(RefCell::new(move |vm: &mut Vm| {
                            dbg!(succ_pc);
                            // This executes only if the dynamic branch succeeds at runtime
                            let succ_thunk_id = vm.new_block();
                            let mut success_types = types.clone();
                            success_types[idx] = expected.clone();
                            vm.compile(orig_pc + 1, success_types.clone(), succ_coro.clone(), ResumeArg::Matched, succ_thunk_id);
                            // Patch the thunk block to jump to the newly specialized block
                            vm.blocks[block_id][succ_pc] = Residual::Jump(succ_thunk_id);
                        })))));
                        return None;
                    }
                }
                CoroutineState::Yielded(YieldOp::Exec(func)) => {
                    self.blocks[block_id].push(Residual::Exec(func));
                    // In a real VM, transition to the next PC generator here.
                    self.blocks[block_id].push(Residual::Ret); 
                    return Some(orig_pc + 1);
                }
                CoroutineState::Complete(_) => {
                    self.blocks[block_id].push(Residual::Ret);
                    return Some(orig_pc + 1);
                }
            }
        }
    }

    pub fn run(&mut self, mut id: BlockId, mut values: Vec<RValue>) -> Vec<RValue> {
        let mut off = 0;
        loop {
            let block = &self.blocks[id];
            let res = block[off].clone();
            dbg!(&res);
            match res {
                Residual::Guard { idx, expected, fail_target } => {
                    if typeof_(&values[idx]) == expected {
                        // Fallthrough
                        off += 2;
                        continue;
                    } else {
                        off = fail_target;
                    }
                },
                Residual::Exec(f) => {
                    f.0(&mut values[..]);
                    off += 1;
                },
                Residual::Jump(target) => {
                    id = target;
                    off = 0;
                },
                Residual::Thunk(thunk) => {
                    dbg!(&block);
                    (thunk.0.borrow_mut())(self)
                },
                Residual::Ret => { return values; },
            }
        }
    }
}

fn main() {
    let mut vm = Vm { code: vec![
        Operation::Add(0, 0, 0),
        Operation::Add(0, 0, 0),
        Operation::Ret,
    ], blocks: vec![], versions: HashMap::new() };

    // 1. Polymorphic compilation (Unknowns) explores the entire CFG.
    let dyn_types = vec![Ty::Unknown, Ty::Unknown, Ty::Unknown];
    //vm.compile(0, dyn_types, emit_add(0, 1, 2), ResumeArg::Start);
    let dyn_block = vm.block(0, dyn_types);
    println!("{:?}", vm.blocks[dyn_block]);
    let res = vm.run(dyn_block, vec![RValue::Int(0), RValue::Int(1), RValue::Int(2)]);
    println!("{:?}", res);

    // 2. Statically known types short-circuits the generator, eliding branches.
    let static_types = vec![Ty::Unknown, Ty::Int, Ty::Int];
    //vm.compile(0, static_types, emit_add(0, 1, 2), ResumeArg::Start);

    println!("{:?}", vm.blocks);
}
