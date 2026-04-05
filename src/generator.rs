#![allow(unused_variables)]

use std::collections::HashMap;
use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;
use std::rc::Rc;
use std::cell::RefCell;

use crate::vm::Opcode;
use qcell::{TCell, TCellOwner};
use crate::vm::{Tc, TcOwner, Vm};
use crate::vm::LClosure;
use crate::vm::{LValue, LType, Number};
use crate::vm::{InstructionDecode, Unpacker};
use crate::vm::RunState;
use crate::chunk::Constant;
use crate::chunk::Instruction;

use log::debug;

fn typeof_<'src, 'intern>(val: &LValue<'src, 'intern>) -> LType {
    match val {
        LValue::Number(_) => LType::Number,
        LValue::InternedString(_) | LValue::OwnedString(_) => LType::String,
        _ => LType::Unknown,
    }
}

#[derive(Debug)]
enum ExecEffect {
    Jump(Pc),
}
type ExecCallback<'a, 'src, 'intern> = &'a mut dyn FnMut(ExecEffect, &mut TCellOwner<TcOwner>, RunState<'src, 'intern>) -> RunState<'src, 'intern>;
#[derive(Clone)]
struct ResidualExec(&'static str, Rc<dyn for <'a, 'src, 'intern> Fn(&mut TCellOwner<TcOwner>, RunState<'src, 'intern>, ExecCallback<'a, 'src, 'intern>) -> RunState<'src, 'intern>>);
impl std::fmt::Debug for ResidualExec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "exec({}, {:p})", self.0, self.1.as_ref() as &_ as *const _ as *const ())
    }
}

#[derive(Clone, Debug)]
pub enum YieldOp {
    Typeof(usize), // Resumed with the type of STACK[idx]
    Guard(usize, LType), // Resumed with either Matched or Failed if STACK[idx] is the expected
                         // type
    GuardRk(usize, LType), // Resumed with either Matched or Failed if STACK[idx] or CONSTANT[idx]
                           // is the expected type
    Exec(ResidualExec), // Emit a residual operation that will be executed
    SetTypes(Vec<(usize, LType)>), // Inform the executor that STACK[idx] = type for each entry
    Jump(usize), // Emit a jump to the given PC, potentially specializing the block if needed.
    GetBlock(Pc), // Resumed with the BlockId for calling the given PC with the current types
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ResumeArg {
    Start,
    Matched,
    Failed,
    Type(LType),
    BlockId(BlockId),
}

pub fn emit_loadk(bx: u32, c: LType, dest: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        match c {
            LType::Number => {
                yield YieldOp::Exec(ResidualExec("loadk_number", Rc::new(move |owner, mut state, cb| {
                    debug!("{:?}", unsafe { &*state.clos.ro(owner).prototype });
                    state.vals[state.base + dest] = unsafe { (&(&(*state.clos.ro(owner).prototype).constants.items)[bx as usize]).into() };
                    state
                })));
                yield YieldOp::SetTypes(vec![(dest, LType::Number)]);
            },
            _ => unreachable!(),
        }
        return arg;
    }
}


pub fn emit_numeric(opcode: Opcode, dest: usize, lhs: usize, rhs: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::GuardRk(lhs, LType::Table);
        if arg == ResumeArg::Matched {
            arg = yield YieldOp::GuardRk(rhs, LType::Table);
            if arg == ResumeArg::Matched {
                yield YieldOp::Exec(ResidualExec("add_table_table", Rc::new(move |owner, mut state, cb| {
                    panic!();
                    state
                })));
                yield YieldOp::SetTypes(vec![(dest, LType::Unknown)]);
                return arg;
            }
        }
        // --- Int Path ---
        arg = yield YieldOp::GuardRk(lhs, LType::Number);
        // TODO: have a MatchedConst case to remove the need for Vm::rk at runtime
        if arg == ResumeArg::Matched {
            arg = yield YieldOp::GuardRk(rhs, LType::Number);
            if arg == ResumeArg::Matched {
                // TODO: is_constant for kb/kc? yeah that's needed for constant type effects
                yield YieldOp::Exec(ResidualExec("add_int_int", Rc::new(move |owner, mut state, cb| {
                    let kb = Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, lhs as u16);
                    let kc = Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, rhs as u16);
                    // Safe bypass of runtime checks
                    debug!("{opcode:?} {kb:?} {kc:?}");
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
                            LValue::from(const_b).numeric_op(opcode, dyn_c).unwrap()
                        },

                        (_, Err(dyn_b), Ok(const_c)) => {
                            dyn_b.numeric_op(opcode, &const_c.into()).unwrap()
                        },

                        (_, Err(dyn_b), Err(dyn_c)) => {
                            dyn_b.numeric_op(opcode, dyn_c).unwrap()
                        },
                        _ => unreachable!(),
                    };
                    debug!("res {:?}", &res);
                    state.vals[state.base + dest as usize] = res;
                    state
                })));
                yield YieldOp::SetTypes(vec![(dest, LType::Number)]);
                return arg;
            }
        }

        // --- Str Path ---
        arg = yield YieldOp::GuardRk(lhs, LType::String);
        if arg == ResumeArg::Matched {
            arg = yield YieldOp::GuardRk(rhs, LType::String);
            if arg == ResumeArg::Matched {
                yield YieldOp::Exec(ResidualExec("add_str_str", Rc::new(move |owner, state, cb| {
                    //let RValue::Str(l) = &vals[lhs] else { unreachable!() };
                    //let RValue::Str(r) = &vals[rhs] else { unreachable!() };
                    //vals[dest] = RValue::Str(l.clone() + r);
                    unimplemented!()
                })));
                yield YieldOp::SetTypes(vec![(dest, LType::String)]);
                return arg;
            } else {
                debug!("fail 2");
            }
        } else {
            debug!("fail 1");
        }

        // --- Generic/Trap Fallback ---
        panic!("Type mismatch trap");
    }
}

pub fn emit_move(dest: usize, src: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Typeof(src);
        if let ResumeArg::Type(t) = arg {
            yield YieldOp::Exec(ResidualExec("move", Rc::new(move |owner, mut state, cb| {
                state.vals[state.base + dest] = state.vals[state.base + src].clone();
                state
            })));
            // TODO: track references? see PyLBBV
            debug!("move {} = {} {:?}", dest, src, t);
            yield YieldOp::SetTypes(vec![(dest, t)]);
        } else {
            unreachable!();
        }
        return arg;
    }
}

pub fn emit_forprep(a: usize, sbx: i32, pc: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        debug!("forprep {a} {sbx} {pc}");
        let mut sub = emit_numeric(Opcode::SUB, a, a, a + 2);
        // TODO: define a macro that does this
        loop {
            let state = Pin::new(&mut sub).resume(arg);
            match state {
                CoroutineState::Yielded(y) => arg = yield y,
                CoroutineState::Complete(_) => break,
            }
        }
        yield YieldOp::Jump(pc + sbx as usize);
        return arg;
    }
}

pub fn emit_forloop(a: usize, sbx: i32, pc: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        debug!("forloop {a} {sbx} {pc}");
        debug!("{} {}", a, sbx);
        let mut sub = emit_numeric(Opcode::ADD, a, a, a + 2);
        let mut mov = emit_move(a, a);
        arg = yield YieldOp::GetBlock(pc);
        let ResumeArg::BlockId(fallthrough) = arg else { unreachable!() };
        arg = yield YieldOp::GetBlock((pc as isize + sbx as isize) as usize);
        let ResumeArg::BlockId(taken) = arg else { unreachable!() };
        yield YieldOp::Exec(ResidualExec("forloop", Rc::new(move |owner, mut state, cb| {
            let idx = state.vals[state.base + a as usize].clone();
            let limit = state.vals[state.base + a as usize + 1].clone();
            let step = state.vals[state.base + a as usize + 2].clone();
            debug!("{:?} {:?} {:?}", idx, limit, step);
            state = cb(ExecEffect::Jump(fallthrough), owner, state);
            state
        })));
        arg
    }
}

pub fn guard_filter(mut sub: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin>) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        loop {
            let state = Pin::new(&mut sub).resume(arg);
            match state {
                CoroutineState::Yielded(y) => arg = yield y,
                CoroutineState::Complete(_) => break,
            }
        }
        return arg;
    }
}

pub type BlockId = usize;
pub type Pc = usize;
#[derive(PartialEq, Eq, Clone, Copy, Hash, Debug)]
pub struct SubPc(usize, usize);

impl SubPc {
    pub fn new(pc: Pc) -> Self {
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
pub struct ThunkRef(pub Rc<RefCell<dyn FnMut(&mut Specializer, &mut TCellOwner<TcOwner>, &mut RunState, usize) -> ()>>);

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

fn filter_coro(mut fresh_coro: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>) -> Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>
{
    Box::new(#[coroutine] move |mut arg: ResumeArg| {
        loop {
            let state = Pin::new(&mut fresh_coro).resume(arg);
            match state {
                CoroutineState::Yielded(y) => arg = yield y,
                CoroutineState::Complete(_) => break,
            }
        }
        return arg;
    })
}

pub struct Specializer<'src, 'intern> {
    pub blocks: Vec<Vec<Residual>>,
    pub clos: Tc<LClosure<'src, 'intern>>,
}

impl<'src, 'intern> Specializer<'src, 'intern> {
    pub fn new(clos: Tc<LClosure<'src, 'intern>>) -> Self {
        Self {
            blocks: Vec::new(),
            clos,
        }
    }

    /// Create a new block at a Lua bytecode PC
    pub fn block(&mut self, owner: &mut TCellOwner<TcOwner>, entry: Pc, types: Vec<LType>) -> BlockId {
        let mut pc = entry;

        let block_id = self.new_block();
        let subpc: SubPc = SubPc::new(entry);
        self.clos.rw(owner).versions.insert((subpc, types.clone()), block_id);
        self.compile(owner, entry, types, block_id);
        return block_id;
    }

    /// Return a specialized block for a given PC and context, compiling a new one if necessary
    pub fn find(&mut self, owner: &mut TCellOwner<TcOwner>, pc: SubPc, types: Vec<LType>) -> Option<BlockId>
    {
        self.clos.ro(owner).versions.get(&(pc, types.clone())).cloned()
    }

    pub fn compile(&mut self, owner: &mut TCellOwner<TcOwner>, mut pc: Pc, mut types: Vec<LType>, block_id: usize) -> Vec<LType> {
        loop {
            let inst = unsafe { self.clos.ro(owner).prototype.as_ref().unwrap().instructions.items[pc].clone() };
            debug!("compile {pc} {:?} {:?}", inst.0.Opcode(), types);
            if let Some((next, ty, ret)) = match inst.0.Opcode() {
                op @ Opcode::ADD => {
                    let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                    debug!("{a} {b} {c}");
                    self.compile_one(owner, SubPc::new(pc), types.clone(), Box::new(emit_numeric(op, a as usize, b as usize, c as usize)), ResumeArg::Start, block_id)
                },
                Opcode::LOADK => {
                    let (a, bx) = crate::vm::ABx::unpack(inst.0);
                    let c: LValue<'src, 'intern> = unsafe { (&(&(*self.clos.ro(owner).prototype).constants.items)[bx as usize]).into() };
                    self.compile_one(owner, SubPc::new(pc), types.clone(), Box::new(emit_loadk(bx, typeof_(&c), a as usize)), ResumeArg::Start, block_id)
                },
                Opcode::MOVE => {
                    let (a, b) = crate::vm::AB::unpack(inst.0);
                    debug!("move {} {}", a, b);
                    self.compile_one(owner, SubPc::new(pc), types.clone(), Box::new(emit_move(a as usize, b as usize)), ResumeArg::Start, block_id)
                },
                Opcode::FORPREP => {
                    let (a, sbx) = crate::vm::AsBx::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), types.clone(), Box::new(emit_forprep(a as usize, sbx, pc + 1)), ResumeArg::Start, block_id)
                },
                Opcode::FORLOOP => {
                    let (a, sbx) = crate::vm::AsBx::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), types.clone(), Box::new(emit_forloop(a as usize, sbx, pc + 1)), ResumeArg::Start, block_id)
                },
                //Operation::Add(o, l, r) => self.compile_one(SubPc::new(pc), types.clone(), emit_add(o, l, r), ResumeArg::Start, block_id),
                Opcode::RETURN => {
                    println!("ret");
                    self.blocks[block_id].push(Residual::Ret); None
                },
                _ => unreachable!(),
            } {
                pc = next;
                types = ty;
                debug!("-> {}", next);
            } else {
                return types;
            }
        }
    }

    pub fn new_block(&mut self) -> BlockId {
        self.blocks.push(Vec::new());
        self.blocks.len() - 1
    }

    // We have to be careful here, where rustc is very unhappy about generator -> thunk ->
    // generator and will either think our types are recursive, require an infinite chain of
    // implications to prove a Coroutine: Clone, or ICE (depending on the time of day) if we use
    // slightly different structure.
    fn yield_one(one: YieldOp) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static {
        #[coroutine] |mut arg: ResumeArg| {
            let arg = yield one;
            debug!("yield one resulted in {arg:?}");
            return arg;
        }
    }

    fn make_thunk(&self, block_id: BlockId, thunk_coro: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>, idx: usize, expected: LType, pc: SubPc, thunk_types: Vec<LType>, appends: bool) -> ThunkRef {

        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut TCellOwner<TcOwner>, state: &mut RunState, thunk_pc: usize| {
            // The thunk was forced, so now we know the runtime value and if it
            // will pass the guard or not.
            // Instead of emitting a guard against `expected`, we can instead just fill in the real
            // type and guard the rest of the generator execution under that as a new block
            // version: if there was a guard against an unknown value and the type would fail, we
            // can be pretty confident that the bytecode operator will try more type guards until
            // it finds the correct one for the type we filled in, and the intermediate guards will
            // be statically false and so not emit any more thunks. Maybe this messes up if
            // bytecode operators don't fully resolve types in a total order? But you can just
            // like, not do that. If needed, there's a jankier version of this that filters the
            // remainder of thunk_coro to hoist specifically the successful type guard for idx in
            // our git history.
            let thunk_coro = thunk_coro.clone();
            let runtime_type = typeof_(&state.vals[state.base + idx]);
            let mut forced_types = thunk_types.clone();
            forced_types[idx] = runtime_type;
            let arg = if runtime_type == expected { ResumeArg::Matched } else { ResumeArg::Failed };
            if !appends {
                // TODO; create a new block and rewrite thunk into a jump instead
                unimplemented!();
            }
            // TODO: search for if we already have a compatible block
            vm.blocks[block_id][thunk_pc] = Residual::Guard { idx, expected: runtime_type };
            // Push the same thunk down for the next value that fails the guard
            let fail_thunk = vm.make_thunk(block_id, thunk_coro.clone(), idx, expected, pc.next_false(), thunk_types.clone(), false);
            vm.blocks[block_id].push(Residual::Thunk(fail_thunk));
            // Finish the remainder of the coroutine
            let guard_block = vm.new_block();
            if let Some((succ_next, succ_ty, succ_ret)) = vm.compile_one(owner, pc.next_true(), forced_types.clone(), thunk_coro, arg, guard_block) {
                // And continue compiling the block
                vm.compile(owner, succ_next, succ_ty, guard_block);
            }
            vm.blocks[block_id].push(Residual::Jump(guard_block));

            debug!("after compiling thunk, blocks look like {:?}", vm.blocks);
        })))
    }

    pub fn compile_one<C>(&mut self, owner: &mut TCellOwner<TcOwner>, mut pc: SubPc, mut types: Vec<LType>, mut coro: Box<C>, mut arg: ResumeArg, block_id: usize) -> Option<(Pc, Vec<LType>, ResumeArg)>
    where C: Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static
    {
        loop {
            let mut state = Pin::new(&mut coro).resume(arg);
            'machine: loop { match state {
                CoroutineState::Yielded(YieldOp::Typeof(idx)) => {
                    arg = ResumeArg::Type(types[idx]);
                },
                CoroutineState::Yielded(YieldOp::GuardRk(rk, ref expected)) => {
                    let proto = self.clos.ro(owner).prototype;
                    if (rk & 0x100)!=0 {
                        let r_const = rk & (0xff);
                        let ty = match unsafe { &(&(*proto).constants.items)[r_const as usize] } {
                            crate::chunk::Constant::Nil => LType::Nil,
                            crate::chunk::Constant::Bool(_) => LType::Bool,
                            crate::chunk::Constant::Number(_) => LType::Number,
                            crate::chunk::Constant::String(_) => LType::String,
                        };
                        debug!("GuardRk constant {:?} {:?}", ty, expected);
                        // Constants always have known types
                        if ty == *expected {
                            pc = pc.next_true();
                            arg = ResumeArg::Matched;
                            break 'machine;
                        } else if ty != LType::Unknown {
                            pc = pc.next_false();
                            arg = ResumeArg::Failed;
                            break 'machine;
                        } else {
                            panic!();
                            state = CoroutineState::Yielded(YieldOp::Guard(rk as usize, expected.clone()));
                            continue 'machine;
                        }
                    } else {
                        debug!("GuardRk dynamic {:?} {:?}", rk, expected);
                        state = CoroutineState::Yielded(YieldOp::Guard(rk as usize, expected.clone()));
                        continue 'machine;
                    }
                },
                CoroutineState::Yielded(guard @ YieldOp::Guard(idx, expected)) => {
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
                        let thunk_coro = coro.clone();
                        let thunk_types = types.clone();
                        let thunk = Residual::Thunk(self.make_thunk(block_id, thunk_coro, idx, expected, pc, thunk_types, true));
                        self.blocks[block_id].push(thunk);
                        return None;
                    }
                }
                CoroutineState::Yielded(YieldOp::Exec(func)) => {
                    self.blocks[block_id].push(Residual::Exec(func));
                    // In a real VM, transition to the next PC generator here.
                }
                CoroutineState::Yielded(YieldOp::SetTypes(ty_effects)) => {
                    for (idx, ty) in ty_effects {
                        if idx > types.len() {
                            types.resize(idx + 1, LType::Unknown);
                        }
                        types[idx] = ty;
                    }
                },
                CoroutineState::Yielded(op @ (YieldOp::GetBlock(dest) | YieldOp::Jump(dest))) => {
                    if let Some(exists) = self.clos.ro(owner).versions.get(&(SubPc::new(dest), types.clone())) {
                        debug!("jump exist {exists}");
                        arg = ResumeArg::BlockId(*exists);
                        if let YieldOp::Jump(dest) = op {
                            self.blocks[block_id].push(Residual::Jump(*exists));
                            return Some((dest, types, ResumeArg::Start));
                        }
                    } else {
                        let fresh = self.new_block();
                        debug!("jump fresh {dest}");
                        self.clos.rw(owner).versions.insert((SubPc::new(dest), types.clone()), fresh);
                        // TODO: do we just return ((dest, types, arg)) here and have self.compile
                        // try to find the block instead? this potentially blows the stack
                        // this should probably push a thunk which compiles the block instead of a
                        // jump
                        self.compile(owner, dest, types.clone(), fresh);
                        arg = ResumeArg::BlockId(fresh);
                        if let YieldOp::Jump(dest) = op {
                            self.blocks[block_id].push(Residual::Jump(fresh));
                            return None;
                        }
                    }
                        // If it was a jump, stop pumping the coroutine
                },
                CoroutineState::Complete(r) => {
                    return Some((pc.0 + 1, types, r));
                }
            } break 'machine; }
        }
    }

    pub fn run(&mut self, owner: &mut TCellOwner<TcOwner>, mut id: BlockId, mut state: RunState<'src, 'intern>) -> RunState<'src, 'intern> {
        let mut off = 0;
        debug!("run");
        loop {
            let block = &self.blocks[id];
            let res = block[off].clone();
            dbg!(&res);
            match res {
                Residual::Guard { idx, expected } => {
                    if typeof_(&state.vals[state.base + idx]) == expected {
                        // Fallthrough
                        off += 2;
                    } else {
                        off += 1;
                    }
                },
                Residual::Exec(f) => {
                    off += 1;
                    state = f.1(owner, state, &mut |eff, owner, state| {
                        debug!("{:?}", eff);
                        match eff {
                            ExecEffect::Jump(block) => {
                                id = block;
                                off = 0;
                            },
                        }
                        state
                    });
                },
                Residual::Jump(target) => {
                    id = target;
                    off = 0;
                },
                Residual::Thunk(thunk) => {
                    dbg!(&block);
                    (thunk.0.borrow_mut())(self, owner, &mut state, off)
                },
                Residual::Ret => {
                    debug!("spec final blocks: {:?}", self.blocks);
                    return state;
                },
            }
        }
    }

    pub fn run_unspec(&mut self, owner: &mut TCellOwner<TcOwner>, mut pc: Pc, mut state: RunState<'src, 'intern>) -> RunState<'src, 'intern> {
        loop {
            let inst = unsafe { self.clos.ro(owner).prototype.as_ref().unwrap().instructions.items[pc].clone() };
            // TODO: figure out a good way to avoid duplicating this with compile()? Kind of
            // difficult because we can't erase the type there...probably need a macro
            let mut coro: Box<dyn Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Unpin> = match inst.0.Opcode() {
                op @ Opcode::ADD => {
                    let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                    debug!("{a} {b} {c}");
                    Box::new(emit_numeric(op, a as usize, b as usize, c as usize))
                },
                Opcode::LOADK => {
                    let (a, bx) = crate::vm::ABx::unpack(inst.0);
                    let c: LValue<'src, 'intern> = unsafe { (&(&(*self.clos.ro(owner).prototype).constants.items)[bx as usize]).into() };
                    Box::new(emit_loadk(bx, typeof_(&c), a as usize))
                },
                Opcode::MOVE => {
                    let (a, b) = crate::vm::AB::unpack(inst.0);
                    debug!("move {} {}", a, b);
                    Box::new(emit_move(a as usize, b as usize))
                },
                Opcode::FORPREP => {
                    let (a, sbx) = crate::vm::AsBx::unpack(inst.0);
                    Box::new(emit_forprep(a as usize, sbx, pc + 1))
                },
                Opcode::FORLOOP => {
                    let (a, sbx) = crate::vm::AsBx::unpack(inst.0);
                    Box::new(emit_forloop(a as usize, sbx, pc + 1))
                },
                //Operation::Add(o, l, r) => self.compile_one(SubPc::new(pc), types.clone(), emit_add(o, l, r), ResumeArg::Start, block_id),
                Opcode::RETURN => {
                    return state
                },
                _ => unreachable!(),
            };
            let mut arg = ResumeArg::Start;
            'run: loop {
                let mut state = Pin::new(&mut coro).resume(arg);
                'machine: loop { match state {
                    CoroutineState::Yielded(guard @ YieldOp::Guard(idx, expected)) => {
                    },
                    _ => unimplemented!(),
                }; break 'machine; }
            }

            panic!();
        }
    }

    // TODO: this is gross! if we spec a block we have to switch current, but then forcing a thunk
    // from another function may at runtime use the wrong current closure. figure out some better
    // way (worse case each block has its own closure and we switch in run when we enter...)
    pub fn set_current(&mut self, clos: Tc<LClosure<'src, 'intern>>) {
        self.clos = clos;
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
