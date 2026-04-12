#![allow(unused_variables)]

use std::borrow::Cow;
use std::collections::HashMap;
use std::ops::{Coroutine, CoroutineState, Deref};
use std::pin::Pin;
use std::rc::Rc;
use std::cell::RefCell;

use crate::vm::{Opcode, Upvalue, CallstackEntry, ReturnLocation};
use qcell::{TCell, TCellOwner};
use crate::vm::{Tc, TcOwner, Vm};
use crate::vm::LClosure;
use crate::vm::{LValue, LType, Number, Table, FVec};
use crate::vm::{InstructionDecode, Unpacker};
use crate::vm::RunState;
use crate::vm::LConstant;
use crate::chunk::Constant;
use crate::chunk::Instruction;

use log::debug;

fn typeof_<'src, 'intern>(val: &LValue<'src, 'intern>) -> LType {
    match val {
        LValue::Number(_) => LType::Number,
        LValue::InternedString(_) | LValue::OwnedString(_) => LType::String,
        LValue::Table(t) => LType::Table,
        LValue::LClosure(_) | LValue::NClosure(_) => LType::Closure,
        LValue::Nil => LType::Nil,
        _ => LType::Unknown,
    }
}

#[derive(Debug)]
enum ExecEffect {
    Jump(BlockId),
    Call(usize, usize, u16),
}
type ExecCallback<'a, 'src, 'intern> = &'a mut dyn for<'b> FnMut(ExecEffect, &mut TCellOwner<TcOwner>, &'b mut RunState<'src, 'intern>);
#[derive(Clone)]
struct ResidualExec(&'static str, Rc<dyn for <'a, 'b, 'src, 'intern> Fn(&mut TCellOwner<TcOwner>, &'b mut RunState<'src, 'intern>, ExecCallback<'a, 'src, 'intern>)>);
impl std::fmt::Debug for ResidualExec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "exec({}, {:p})", self.0, self.1.as_ref() as &_ as *const _ as *const ())
    }
}

#[derive(Clone, Debug)]
pub enum CallTarget {
    Dynamic(usize, usize, usize),
    Concrete(Pc),
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
    Jump(BlockId), // Emit a jump to the given BlockId
    GetBlock(Pc), // Resumed with the BlockId for calling the given PC with the current types
    Call(CallTarget), // Call a block target. Probably need a ResumeArg for returned values later.
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ResumeArg {
    Start,
    Matched,
    MatchedConst(usize),
    Failed,
    Type(LType),
    BlockId(BlockId),
}

pub fn emit_loadk(bx: u32, c: LType, dest: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        match c {
            LType::Number => {
                yield YieldOp::Exec(ResidualExec("loadk_number", Rc::new(move |owner, state, cb| {
                    let kst = unsafe { &(&(*state.clos.ro(owner).prototype).constants.items)[bx as usize] };
                    debug!("{:?}", kst);
                    state.vals[state.base + dest] = kst.into();
                })));
                yield YieldOp::SetTypes(vec![(dest, LType::Number)]);
            },
            LType::String => {
                yield YieldOp::Exec(ResidualExec("loadk_str", Rc::new(move |owner, state, cb| {
                    let kst = unsafe { &(&(*state.clos.ro(owner).prototype).constants.items)[bx as usize] };
                    debug!("{:?}", kst);
                    state.vals[state.base + dest] = kst.into();
                })));
                yield YieldOp::SetTypes(vec![(dest, LType::String)]);
            },
            _ => unreachable!(),
        }
        return arg;
    }
}

pub fn emit_getglobal<'src, 'intern>(dest: usize, kst: &LConstant<'src, 'intern>) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static {
    // We need unsafe here, because we can't prove to rustc that this Rc<Fn> won't outlive
    // 'src and 'intern which it refers to. We only ever store these closures in the
    // closure object which itself borrows from the same data, and so this is safe.
    let kst: LConstant<'static, 'static> = unsafe { core::mem::transmute(kst.clone()) };
    #[coroutine]
    move |mut arg: ResumeArg| {
        // TODO: env shape specialization
        // maybe getting _G[kst] should be a yieldop...?
        debug!("getglobal {} = {:?}", dest, &kst);
        yield YieldOp::Exec(ResidualExec("getglobal", Rc::new(move |owner, state, cb| {
            state.vals[state.base + dest as usize] = state._G.get(owner, &(&kst).into()).unwrap_or((&Constant::Nil).into()).clone();
        })));
        yield YieldOp::SetTypes(vec![(dest, LType::Unknown)]);
        arg
    }
}

pub fn emit_setglobal<'src, 'intern>(dest: usize, kst: &LConstant<'src, 'intern>) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static {
    // We need unsafe for the same reason, and with the same justification, as emit_getglobal.
    let kst: LConstant<'static, 'static> = unsafe { core::mem::transmute(kst.clone()) };
    #[coroutine]
    move |mut arg: ResumeArg| {
        // TODO: env shape specialization
        debug!("setglobal {} = {:?}", dest, &kst);
        yield YieldOp::Exec(ResidualExec("setglobal", Rc::new(move |owner, state, cb| {
            state._G.set(owner, (&kst).into(), state.vals[state.base + dest as usize].clone());
        })));
        arg
    }
}

pub fn emit_gettable(a: usize, b: usize, c: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Guard(b, LType::Table);
        if arg != ResumeArg::Matched {
            arg = yield YieldOp::Exec(ResidualExec("gettable_meta", Rc::new(move |owner, state, cb| {
                panic!("gettable_meta {:?} {:?}", &state.vals, &state.vals[state.base + b])
            })));
            yield YieldOp::SetTypes(vec![(a, LType::Unknown)]);
            return arg;
        }
        // TODO: object shape specialization
        arg = yield YieldOp::Exec(ResidualExec("gettable", Rc::new(move |owner, state, cb| {
            let kc = match Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, c as u16) {
                Ok(c) => Cow::Owned(LValue::from(c)),
                Err(lv) => Cow::Borrowed(lv),
            };
            debug!("gettable {:?}", &kc);
            let val_b = state.vals[state.base + b as usize].clone();
            state.vals[state.base + a as usize] = val_b.gettable(owner, kc);
        })));
        yield YieldOp::SetTypes(vec![(a, LType::Unknown)]);
        arg
    }
}

pub fn emit_settable(a: usize, b: usize, c: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Guard(a, LType::Table);
        if arg != ResumeArg::Matched {
            arg = yield YieldOp::Exec(ResidualExec("settable_meta", Rc::new(move |owner, state, cb| {
                panic!("settable_meta {:?}", state.vals)
            })));
            return arg;
        }
        // TODO: table shape specialization
        arg = yield YieldOp::GuardRk(b, LType::Number);
        if let ResumeArg::Matched | ResumeArg::MatchedConst(_) = arg {
            // Array part set
            // TODO: MatchedConst
            arg = yield YieldOp::Exec(ResidualExec("settable_array", Rc::new(move |owner, state, cb| {
                let kb = match Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, b as u16) {
                    Ok(b) => b.into(),
                    Err(lv) => lv.clone(),
                };
                let LValue::Number(kb) = kb else { unreachable!() };
                let kc = match Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, c as u16) {
                    Ok(c) => c.into(),
                    Err(lv) => lv.clone(),
                };
                let LValue::Table(t) = &mut state.vals[state.base + a] else { unreachable!() };
                let t = t.rw(owner);
                if t.array.len() <= kb.0 as usize {
                    t.array.resize_with(kb.0 as usize, || LValue::Nil);
                }
                t.array[kb.0 as usize-1] = kc;
            })));
        } else {
            // Hash part set
            arg = yield YieldOp::Exec(ResidualExec("settable_hash", Rc::new(move |owner, state, cb| {
                let kb = match Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, b as u16) {
                    Ok(b) => b.into(),
                    Err(lv) => lv.clone(),
                };
                let kc = match Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, c as u16) {
                    Ok(c) => c.into(),
                    Err(lv) => lv.clone(),
                };
                let LValue::Table(t) = &mut state.vals[state.base + a] else { unreachable!() };
                t.rw(owner).hash.insert(kb, kc);
            })));
        }
        arg
    }
}

pub fn emit_newtable(a: usize, b: usize, c: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Exec(ResidualExec("newtable", Rc::new(move |owner, state, cb| {
            // TODO: properly decode the "floating point byte" size hints instead
            state.vals[state.base + a as usize] = LValue::Table(Tc::new(Table::new(b as usize, c as usize)));
        })));
        yield YieldOp::SetTypes(vec![(a, LType::Table)]);
        arg
    }
}

pub fn emit_setlist(a: usize, b: usize, c: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        // We don't need to guard on LType::Table, because this instruction is only ever used for
        // table initialization, which means it is definitely a table and doesn't e.g. have a
        // metatable we have to chain to.
        arg = yield YieldOp::Exec(ResidualExec("setlist", Rc::new(move |owner, state, cb| {
            match state.vals[state.base + a as usize].clone() {
                LValue::Table(tab) => {
                    assert_ne!(c, 0);
                    if b == 0 {
                        let src = state.vals[state.base + a as usize+1..].iter().cloned();
                        tab.rw(owner).array.splice(
                            (c as usize-1)*50..,
                            src
                        ).for_each(drop);
                    } else {
                        let src = state.vals[state.base + a as usize+1..=state.base + a as usize+b as usize as usize].iter().cloned();
                        tab.rw(owner).array.splice(
                            (c as usize-1)*50..,
                            src
                        ).for_each(drop);
                    }
                },
                _ => unreachable!(),
            };
        })));
        yield YieldOp::SetTypes(vec![(a, LType::Table)]);
        arg
    }
}

pub fn emit_numeric(opcode: Opcode, dest: usize, lhs: usize, rhs: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::GuardRk(lhs, LType::Table);
        if let ResumeArg::Matched | ResumeArg::MatchedConst(_) = arg {
            arg = yield YieldOp::GuardRk(rhs, LType::Table);
            if let ResumeArg::Matched | ResumeArg::MatchedConst(_) = arg {
                yield YieldOp::Exec(ResidualExec("numeric_table_table", Rc::new(move |owner, state, cb| {
                    panic!();
                })));
                yield YieldOp::SetTypes(vec![(dest, LType::Unknown)]);
                return arg;
            }
        }
        // --- Int Path ---
        let larg = yield YieldOp::GuardRk(lhs, LType::Number);
        let rarg = yield YieldOp::GuardRk(rhs, LType::Number);
        arg = rarg;
        match (larg, rarg) {
            (ResumeArg::Matched, ResumeArg::Matched) => {
                yield YieldOp::Exec(ResidualExec("numeric_int_int", Rc::new(move |owner, state, cb| {
                    let klhs = Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, lhs as u16);
                    let krhs = Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, rhs as u16);
                    let LValue::Number(dyn_b) = &state.vals[state.base + lhs] else { unreachable!() };
                    let LValue::Number(dyn_c) = &state.vals[state.base + rhs] else { unreachable!() };
                    let res = LValue::Number(*dyn_b).numeric_op(opcode, &LValue::Number(*dyn_c)).unwrap();
                    debug!("res {:?}", &res);
                    state.vals[state.base + dest as usize] = res;
                })));
                yield YieldOp::SetTypes(vec![(dest, LType::Number)]);
                return arg;
            },
            (ResumeArg::MatchedConst(lhsc), ResumeArg::MatchedConst(rhsc)) => {
                yield YieldOp::Exec(ResidualExec("numeric_cint_cint", Rc::new(move |owner, state, cb| {
                    let klhs: &LConstant = unsafe { &((&(*state.clos.ro(owner).prototype).constants.items)[lhsc as usize]) };
                    let krhs: &LConstant = unsafe { &((&(*state.clos.ro(owner).prototype).constants.items)[rhsc as usize]) };
                    let LConstant::Number(kb) = klhs else { unreachable!() };
                    let LConstant::Number(kc) = krhs else { unreachable!() };
                    let res = LValue::Number(*kb).numeric_op(opcode, &LValue::Number(*kc)).unwrap();
                    debug!("res {:?}", &res);
                    state.vals[state.base + dest as usize] = res;
                })));
                yield YieldOp::SetTypes(vec![(dest, LType::Number)]);
                return arg;
            },
            (ResumeArg::MatchedConst(lhsc), ResumeArg::Matched) => {
                yield YieldOp::Exec(ResidualExec("numeric_cint_int", Rc::new(move |owner, state, cb| {
                    let kb: &LConstant = unsafe { &((&(*state.clos.ro(owner).prototype).constants.items)[lhsc as usize]) };
                    let LConstant::Number(kb) = kb else { unreachable!() };
                    let dyn_c = &state.vals[state.base + rhs];
                    let res = LValue::Number(Number(kb.0)).numeric_op(opcode, dyn_c).unwrap();
                    debug!("res {:?}", &res);
                    state.vals[state.base + dest as usize] = res;
                })));
                yield YieldOp::SetTypes(vec![(dest, LType::Number)]);
                return arg;
            },
            (ResumeArg::Matched, ResumeArg::MatchedConst(rhsc)) => {
                yield YieldOp::Exec(ResidualExec("numeric_int_cint", Rc::new(move |owner, state, cb| {
                    let dyn_b = &state.vals[state.base + lhs];
                    let kc: &LConstant = unsafe { &((&(*state.clos.ro(owner).prototype).constants.items)[rhsc as usize]) };
                    let LConstant::Number(kc) = kc else { unreachable!() };
                    let res = dyn_b.numeric_op(opcode, &LValue::Number(Number(kc.0))).unwrap();
                    debug!("res {:?}", &res);
                    state.vals[state.base + dest as usize] = res;
                })));
                yield YieldOp::SetTypes(vec![(dest, LType::Number)]);
                return arg;
            },
            _ => { /* fallthrough */ },
        }

        // --- Str Path ---
        arg = yield YieldOp::GuardRk(lhs, LType::String);
        if let ResumeArg::Matched | ResumeArg::MatchedConst(_) = arg {
            arg = yield YieldOp::GuardRk(rhs, LType::String);
            if let ResumeArg::Matched | ResumeArg::MatchedConst(_) = arg {
                yield YieldOp::Exec(ResidualExec("numeric_str_str", Rc::new(move |owner, state, cb| {
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

pub fn emit_compare(opcode: Opcode, a: u8, b: usize, c: usize, pc: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        let larg = yield YieldOp::GuardRk(b, LType::Number);
        let rarg = yield YieldOp::GuardRk(c, LType::Number);
        arg = rarg;

        arg = yield YieldOp::GetBlock(pc);
        let ResumeArg::BlockId(fallthrough) = arg else { unreachable!() };
        arg = yield YieldOp::GetBlock((pc as isize + 1 as isize) as usize);
        let ResumeArg::BlockId(taken) = arg else { unreachable!() };

        match (larg, rarg) {
            (ResumeArg::Matched, ResumeArg::Matched) => {
                unimplemented!()
            },
            (ResumeArg::MatchedConst(rb), ResumeArg::Matched) => {
                arg = yield YieldOp::Exec(ResidualExec("comp_cint_int", Rc::new(move |owner, state, cb| {
                    debug!("comp @ {}", pc);
                    let const_b = unsafe { &(&(*state.clos.ro(owner).prototype).constants.items)[rb as usize] };
                    let Constant::Number(Number(_)) = const_b else { unreachable!() };
                    let dyn_c = &state.vals[state.base + c];
                    let cond = LValue::from(const_b).compare(opcode, dyn_c.clone()).unwrap();
                    if (cond as u8) != a {
                        debug!("taking comparison jump -> {:?}", taken);
                        cb(ExecEffect::Jump(taken), owner, state);
                    } else {
                        debug!("falling through comparison jump -> {:?}", fallthrough);
                        cb(ExecEffect::Jump(fallthrough), owner, state);
                    }
                })));
            },
            (ResumeArg::Matched, ResumeArg::MatchedConst(rc)) => {
                arg = yield YieldOp::Exec(ResidualExec("comp_int_cint", Rc::new(move |owner, state, cb| {
                    debug!("comp @ {}", pc);
                    let dyn_b = &state.vals[state.base + b];
                    let const_c = unsafe { &(&(*state.clos.ro(owner).prototype).constants.items)[rc as usize] };
                    let Constant::Number(Number(_)) = const_c else { unreachable!() };
                    let cond = dyn_b.compare(opcode, const_c.into()).unwrap();
                    if (cond as u8) != a {
                        debug!("taking comparison jump -> {:?}", taken);
                        cb(ExecEffect::Jump(taken), owner, state);
                    } else {
                        debug!("falling through comparison jump -> {:?}", fallthrough);
                        cb(ExecEffect::Jump(fallthrough), owner, state);
                    }
                })));
            },
            (ResumeArg::MatchedConst(rb), ResumeArg::MatchedConst(rc)) => {
                unimplemented!()
            },
            _ => unreachable!(),
        }
        arg = yield YieldOp::Jump(fallthrough);
        arg
    }
}

pub fn emit_jmp(sbx: i32, pc: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::GetBlock(((pc as isize) + sbx as isize) as usize);
        let ResumeArg::BlockId(target) = arg else { unreachable!() };
        arg = yield YieldOp::Jump(target);
        arg
    }
}


pub fn emit_unm(a: usize, b: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::GuardRk(b, LType::Number);
        let (ResumeArg::Matched | ResumeArg::MatchedConst(_)) = arg else {
            unimplemented!("__unm metatable");
        };
        arg = yield YieldOp::Exec(ResidualExec("unm", Rc::new(move |owner, state, cb| {
            let res = match &state.vals[state.base + b as usize] {
                // TODO: metatables
                LValue::Number(n) => LValue::Number(Number(-n.0)),
                _ => unimplemented!(),
            };
            state.vals[state.base + a as usize] = res;
        })));
        yield YieldOp::SetTypes(vec![(a, LType::Number)]);
        arg
    }
}

pub fn emit_len(a: usize, b: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Guard(b, LType::String);
        if ResumeArg::Matched == arg {
            arg = yield YieldOp::Exec(ResidualExec("len_str", Rc::new(move |owner, state, cb| {
                let b = &state.vals[state.base + b];
                let n = match b {
                    LValue::OwnedString(s) => { s.len() },
                    LValue::InternedString(s) => { s.0.len() },
                    _ => unreachable!(),
                };
                state.vals[state.base + a] = LValue::Number(Number(n as _));
            })));
            yield YieldOp::SetTypes(vec![(a, LType::Number)]);
            return arg;
        }
        arg = yield YieldOp::Guard(b, LType::Table);
        if ResumeArg::Matched == arg {
            // TODO: __len metamethod
            arg = yield YieldOp::Exec(ResidualExec("len_str", Rc::new(move |owner, state, cb| {
                let LValue::Table(b) = &state.vals[state.base + b] else { unreachable!() };
                let n = b.ro(owner).array.len();
                state.vals[state.base + a] = LValue::Number(Number(n as _));
            })));
            yield YieldOp::SetTypes(vec![(a, LType::Number)]);
            return arg;
        } else {
            unimplemented!("__len metamethod")
        }

        arg
    }
}


pub fn emit_move(dest: usize, src: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Typeof(src);
        if let ResumeArg::Type(t) = arg {
            yield YieldOp::Exec(ResidualExec("move", Rc::new(move |owner, state, cb| {
                state.vals[state.base + dest] = state.vals[state.base + src].clone();
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

macro_rules! drain {
    ($i:ident, $arg:ident) => {
        $arg = ResumeArg::Start;
        loop {
            let state = Pin::new(&mut $i).resume($arg);
            match state {
                CoroutineState::Yielded(y) => $arg = yield y,
                CoroutineState::Complete(_) => break,
            }
        }
    }
}


pub fn emit_getupval(a: usize, b: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Exec(ResidualExec("getupval", Rc::new(move |owner, state, cb| {
            let upval = match state.clos.ro(owner).upvalues[b as usize].borrow().deref() {
                Upvalue::Open(o) => {
                    state.vals[*o as usize].clone()
                },
                Upvalue::Closed(c) => {
                    c.borrow().clone()
                },
            };
            debug!("upval {:?}", &upval);
            state.vals[state.base + a as usize] = upval;
            debug!("after getupval {:?}", &state.vals[state.base..]);
        })));
        // TODO: We could keep a static upval typemap, since you can't transition the type of an
        // upval after its created.
        arg = yield YieldOp::SetTypes(vec![(a, LType::Unknown)]);
        return arg;
    }
}



pub fn emit_forprep(a: usize, sbx: i32, pc: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        debug!("forprep {a} {sbx} {pc}");
        let mut sub = emit_numeric(Opcode::SUB, a, a, a + 2);
        drain!(sub, arg);
        arg = yield YieldOp::GetBlock(((pc as isize) + sbx as isize) as usize);
        let ResumeArg::BlockId(target) = arg else { unreachable!() };
        yield YieldOp::Jump(target);
        return arg;
    }
}

pub fn emit_forloop(a: usize, sbx: i32, pc: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        debug!("forloop {a} {sbx} {pc}");
        debug!("{} {}", a, sbx);
        let mut sub = emit_numeric(Opcode::ADD, a, a, a + 2);
        drain!(sub, arg);
        let mut mov = emit_move(a, a);
        drain!(mov, arg);
        // TODO: `comp` metamethods? which may invalidate the types that our resolved
        // blocks are compatible for? i think they're fine because they're on the stack whatever
        arg = yield YieldOp::GetBlock(pc);
        let ResumeArg::BlockId(fallthrough) = arg else { unreachable!() };
        arg = yield YieldOp::GetBlock((pc as isize + sbx as isize) as usize);
        let ResumeArg::BlockId(taken) = arg else { unreachable!() };
        yield YieldOp::Exec(ResidualExec("forloop", Rc::new(move |owner, state, cb| {
            let idx = state.vals[state.base + a as usize].clone();
            let limit = state.vals[state.base + a as usize + 1].clone();
            let step = state.vals[state.base + a as usize + 2].clone();
            debug!("{:?} {:?} {:?}", idx, limit, step);
            let comp = if step.compare(Opcode::LT, LValue::from(&Constant::Number(Number(0.0)))).unwrap() {
                limit.compare(Opcode::LE, idx.clone())
            } else {
                idx.clone().compare(Opcode::LE, limit)
            };
            if comp.unwrap() {
                cb(ExecEffect::Jump(taken), owner, state);
                state.vals[state.base + a as usize + 3] = idx;
            } else {
                cb(ExecEffect::Jump(fallthrough), owner, state);
            }
        })));
        arg
    }
}

pub fn emit_call(a: usize, b: usize, c: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Guard(a, LType::Closure);
        if arg != ResumeArg::Matched {
            arg = yield YieldOp::Exec(ResidualExec("call_meta", Rc::new(move |owner, state, cb| {
                panic!("call metamethod {} {:?} {:?}", b, &state.vals, &state.vals[state.base + b])
            })));
            return arg;
        }
        // TODO: track concrete function targets at the type level, and emit a YieldOp::Dispatch
        // guard here for specializing the call + return continuation for each one.
        arg = yield YieldOp::Call(CallTarget::Dynamic(a, b, c));
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

#[derive(PartialEq, Eq, Clone, Copy, Hash, Debug)]
pub struct BlockId(pub usize);
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
    Call(BlockId, usize, usize),
    Jump(BlockId),
    Thunk(ThunkRef),
    Ret(Pc, u8, u16),
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
        let count: Vec<_> = self.clos.ro(owner).versions.iter().filter(|((pc, ty), block)| pc.0 == entry).collect();
        if count.len() >= 5 {
            panic!("too many versions: {:?}", count);
        }
        self.clos.rw(owner).versions.insert((subpc, types.clone()), block_id);
        self.compile(owner, entry, types, block_id);
        return block_id;
    }

    /// Return a specialized block for a given PC and context, compiling a new one if necessary
    pub fn find(&mut self, owner: &mut TCellOwner<TcOwner>, pc: SubPc, types: &Vec<LType>) -> Option<BlockId>
    {
        self.clos.ro(owner).versions.get(&(pc, types.clone())).cloned()
    }

    pub fn compile(&mut self, owner: &mut TCellOwner<TcOwner>, mut pc: Pc, mut types: Vec<LType>, block_id: BlockId) -> Vec<LType> {
        loop {
            let inst = unsafe { self.clos.ro(owner).prototype.as_ref().unwrap().instructions.items[pc].clone() };
            debug!("compile {pc} {:?} {:?}", inst.0.Opcode(), types);
            if let Some((next, ty, ret)) = match inst.0.Opcode() {
                op @ (Opcode::ADD | Opcode::SUB | Opcode::MUL | Opcode::DIV | Opcode::MOD | Opcode::POW) => {
                    let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                    debug!("{a} {b} {c}");
                    self.compile_one(owner, SubPc::new(pc), types.clone(), Box::new(emit_numeric(op, a as usize, b as usize, c as usize)), ResumeArg::Start, block_id)
                },
                op @ (Opcode::EQ | Opcode::LT | Opcode::LE) => {
                    let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                    debug!("{a} {b} {c}");
                    self.compile_one(owner, SubPc::new(pc), types.clone(), Box::new(emit_compare(op, a, b as usize, c as usize, pc + 1)), ResumeArg::Start, block_id)
                },
                Opcode::JMP => {
                    let sbx = crate::vm::sBx::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), types.clone(), Box::new(emit_jmp(sbx, pc + 1)), ResumeArg::Start, block_id)
                    //self.blocks[block_id].push(Residual::Jump(((pc as isize) + sbx as isize) as usize)); return types;
                },
                Opcode::UNM => {
                    let (a, b) = crate::vm::AB::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), types.clone(), Box::new(emit_unm(a as usize, b as usize)), ResumeArg::Start, block_id)
                },
                Opcode::LEN => {
                    let (a, b) = crate::vm::AB::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), types.clone(), Box::new(emit_len(a as usize, b as usize)), ResumeArg::Start, block_id)
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
                Opcode::GETUPVAL => {
                    let (a, b) = crate::vm::AB::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), types.clone(), Box::new(emit_getupval(a as usize, b as usize)), ResumeArg::Start, block_id)
                },
                Opcode::CALL => {
                    let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                    debug!("{} {} {}", a, b, c);
                    // TODO: this should try to compile a new block and jump to it, and only
                    // fallback to a trace exit if we need to run the fully generic code
                    self.compile_one(owner, SubPc::new(pc), types.clone(), Box::new(emit_call(a as usize, b as usize, c as usize)), ResumeArg::Start, block_id)
                },
                Opcode::GETGLOBAL => {
                    let (a, bx) = crate::vm::ABx::unpack(inst.0);
                    let kst = unsafe { &(&(*self.clos.ro(owner).prototype).constants.items)[bx as usize] };
                    debug!("getglobal {} {} {:?}", a, bx, &kst);
                    self.compile_one(owner, SubPc::new(pc), types.clone(), Box::new(emit_getglobal(a as usize, kst)), ResumeArg::Start, block_id)
                },
                Opcode::SETGLOBAL => {
                    let (a, bx) = crate::vm::ABx::unpack(inst.0);
                    let kst = unsafe { &(&(*self.clos.ro(owner).prototype).constants.items)[bx as usize] };
                    self.compile_one(owner, SubPc::new(pc), types.clone(), Box::new(emit_setglobal(a as usize, kst)), ResumeArg::Start, block_id)
                },
                Opcode::GETTABLE => {
                    let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                    debug!("gettable {} {} {}", a, b, c);
                    self.compile_one(owner, SubPc::new(pc), types.clone(), Box::new(emit_gettable(a as usize, b as usize, c as usize)), ResumeArg::Start, block_id)
                },
                Opcode::SETTABLE => {
                    let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                    debug!("settable {} {} {}", a, b, c);
                    self.compile_one(owner, SubPc::new(pc), types.clone(), Box::new(emit_settable(a as usize, b as usize, c as usize)), ResumeArg::Start, block_id)
                },
                Opcode::NEWTABLE => {
                    let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), types.clone(), Box::new(emit_newtable(a as usize, b as usize, c as usize)), ResumeArg::Start, block_id)
                },
                Opcode::SETLIST => {
                    let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), types.clone(), Box::new(emit_setlist(a as usize, b as usize, c as usize)), ResumeArg::Start, block_id)
                },
                Opcode::RETURN => {
                    let (a, b) = crate::vm::AB::unpack(inst.0);
                    self.blocks[block_id.0].push(Residual::Ret(pc, a, b)); None
                },
                x => {
                    #[cfg(debug_assertions)]
                    {
                        unreachable!("{:?}", x)
                    }
                    panic!();
                    self.blocks[block_id.0].push(Residual::Ret(pc, 0, 0)); None
                },
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
        BlockId(self.blocks.len() - 1)
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
            debug!("forcing thunk with {:?} == {:?}", runtime_type, expected);
            let arg = if runtime_type == expected { ResumeArg::Matched } else { ResumeArg::Failed };
            if !appends {
                // TODO; create a new block and rewrite thunk into a jump instead
                unimplemented!("{:?}", runtime_type);
            }
            // TODO: search for if we already have a compatible block
            vm.blocks[block_id.0][thunk_pc] = Residual::Guard { idx, expected: runtime_type };
            // Push the same thunk down for the next value that fails the guard
            let fail_thunk = vm.make_thunk(block_id, thunk_coro.clone(), idx, expected, pc.next_false(), thunk_types.clone(), false);
            vm.blocks[block_id.0].push(Residual::Thunk(fail_thunk));
            // Finish the remainder of the coroutine
            let guard_block = vm.new_block();
            if let Some((succ_next, succ_ty, succ_ret)) = vm.compile_one(owner, pc.next_true(), forced_types.clone(), thunk_coro, arg, guard_block) {
                // And continue compiling the block
                vm.compile(owner, succ_next, succ_ty, guard_block);
            }
            vm.blocks[block_id.0].push(Residual::Jump(guard_block));

            debug!("after compiling thunk, blocks look like {:?}", vm.blocks);
        })))
    }

    pub fn compile_one<C>(&mut self, owner: &mut TCellOwner<TcOwner>, mut pc: SubPc, mut types: Vec<LType>, mut coro: Box<C>, mut arg: ResumeArg, block_id: BlockId) -> Option<(Pc, Vec<LType>, ResumeArg)>
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
                            arg = ResumeArg::MatchedConst(r_const);
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
                    debug!("guard {:?} == {:?}", types[idx], expected);
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
                        self.blocks[block_id.0].push(thunk);
                        return None;
                    }
                }
                CoroutineState::Yielded(YieldOp::Exec(func)) => {
                    self.blocks[block_id.0].push(Residual::Exec(func));
                    // In a real VM, transition to the next PC generator here.
                },
                CoroutineState::Yielded(YieldOp::Call(target)) => {
                    let id;
                    match target {
                        CallTarget::Concrete(target) => {
                            // TODO: suspend coro so that it can be resumed after the target returns to
                            // compile the continuation
                            panic!();
                            if let Some(exists) = self.find(owner, SubPc::new(target), &types) {
                                id = exists;
                            } else {
                                debug!("compiling fresh callsite {} {:?}", target, types);
                                id = self.block(owner, target, types);
                            }
                        },
                        CallTarget::Dynamic(a, b, c) => {
                            let call_exec = Residual::Exec(ResidualExec("call", Rc::new(move |owner, state, cb| {
                                cb(ExecEffect::Call(a, b, c as u16), owner, state);
                            })));
                            self.blocks[block_id.0].push(call_exec);
                            let types = if c == 1 {
                                // No values are saved
                                // All our types are intact
                                types
                            } else if c >= 2 {
                                // (C-1) values are saved
                                // Returned values become unknown
                                // TODO: compile a type specialized thunk instead? is that better?
                                for i in 0..(c - 1) {
                                    types[a + i] = LType::Unknown;
                                }
                                types
                            } else {
                                // Multiple return results are saved
                                // All types until end of stack are unknown
                                for i in a..types.len() {
                                    types[i] = LType::Unknown;
                                }
                                types
                            };
                            //types = vec![LType::Unknown; types.len()];
                            return Some((pc.0 + 1, types, ResumeArg::Start));
                        },
                    }
                },
                CoroutineState::Yielded(YieldOp::SetTypes(ty_effects)) => {
                    for (idx, ty) in ty_effects {
                        if idx > types.len() {
                            types.resize(idx + 1, LType::Unknown);
                        }
                        types[idx] = ty;
                    }
                },
                CoroutineState::Yielded(YieldOp::GetBlock(dest_pc)) => {
                    if let Some(exists) = self.clos.ro(owner).versions.get(&(SubPc::new(dest_pc), types.clone())) {
                        debug!("jump exist {dest_pc} -> {exists:?}");
                        arg = ResumeArg::BlockId(*exists);
                    } else {
                        let fresh = self.new_block();
                        debug!("jump fresh {dest_pc} -> {:?}", fresh);
                        self.clos.rw(owner).versions.insert((SubPc::new(dest_pc), types.clone()), fresh);
                        // TODO: do we just return ((dest, types, arg)) here and have self.compile
                        // try to find the block instead? this potentially blows the stack
                        // this should probably push a thunk which compiles the block instead of a
                        // jump
                        self.compile(owner, dest_pc, types.clone(), fresh);
                        arg = ResumeArg::BlockId(fresh);
                    }
                },
                CoroutineState::Yielded(YieldOp::Jump(dest_block)) => {
                    self.blocks[block_id.0].push(Residual::Jump(dest_block));
                    // If it was a jump, stop pumping the coroutine
                    return None;
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
            let block = &self.blocks[id.0];
            let res = block[off].clone();
            state.counters.versioned_count.increment();
            debug!("{:?}", &res);
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
                    f.1(owner, &mut state, &mut |eff, owner, state| {
                        debug!("{:?}", eff);
                        match eff {
                            ExecEffect::Jump(block) => {
                                id = block;
                                off = 0;
                            },
                            ExecEffect::Call(a, b, c) => {
                                // Dynamic dispatch call
                                let to_call = &state.vals[state.base + a as usize];
                                if let LValue::LClosure(ref lclos) = to_call.clone() {
                                    // record call stack: we say where to return to and where to put the values
                                    let next_stack = unsafe { (*lclos.ro(owner).prototype).max_stack as usize };
                                    // push empty stack frame
                                    state.vals.extend_from_slice(
                                        vec![LValue::Nil; next_stack].as_slice());
                                    state.callstack.push(CallstackEntry(self.clos.clone(), ReturnLocation::Generator(id, off), state.base, state.vals.len(), state.base + a, c));
                                    state.base = state.base + a as usize + 1;
                                    state.vals.truncate(state.base +  next_stack);
                                    state.clos = lclos.clone();

                                    // Either use existing block, compile a new one, or use most
                                    // generic.
                                    let types = vec![LType::Unknown; next_stack];
                                    let block = if let Some(block) = lclos.ro(owner).versions.get(&(SubPc::new(0), types.clone())) {
                                        *block
                                    } else {
                                        debug!("compiling fresh callsite {:?} {:?}", unsafe { &(*lclos.ro(owner).prototype).source }, types);
                                        self.set_current(lclos.clone());
                                        self.block(owner, 0, types)
                                    };
                                    debug!("{:?} {block:?}", self.blocks);
                                    self.set_current(lclos.clone());
                                    id = block;
                                    off = 0;
                                } else if let LValue::NClosure(ncall) = to_call {
                                    let args = if b == 0 {
                                        &state.vals[state.base + a as usize+1..]
                                    } else {
                                        &state.vals[state.base + a as usize+1..=(state.base + a as usize + b as usize - 1)]
                                    };
                                    debug!("{:?}", args);
                                    let mut native = ncall.rw(owner).native.clone();
                                    let ret = (native)(args, owner);
                                    if c == 0 {
                                        // save all returned
                                        state.vals.splice(state.base + a as usize.., ret).for_each(drop);
                                    }
                                    else if c == 1 {
                                        // nothing saved
                                    } else if c != 1 {
                                        state.vals.splice(state.base + a as usize..state.base + a as usize + c as usize - 2, ret).for_each(drop);
                                    } else {
                                        unimplemented!()
                                    }
                                }
                            },
                        }
                    });
                },
                Residual::Jump(target) => {
                    id = target;
                    off = 0;
                },
                Residual::Call(target, a, c) => {
                    // Static dispatch call
                    //state.callstack.push(CallstackEntry(self.clos.clone(), ReturnLocation::Generator(id, off), state.base, state.vals.len(), state.base + a, c));
                    panic!("push callstack");
                    //state.clos.clone(), state.pc, state.base, state.vals.len(), state.base + a as usize, c
                    id = target;
                    off = 0;
                },
                Residual::Thunk(thunk) => {
                    debug!("thunk {:?}", &block);
                    (thunk.0.borrow_mut())(self, owner, &mut state, off)
                },
                Residual::Ret(pc, a, b) => {
                    debug!("spec final blocks: {:?}", self.blocks);
                    state.close_upvalues();
                    state.upvals = vec![].into();
                    let mut r_count = 0 as usize;
                    let mut r_vals: FVec<_> = if b == 1 {
                        // no return values
                        vec![].into()
                    } else if b >= 2 {
                        // there are b-1 return values from R(A) onwards
                        r_count = b as usize-1;
                        let r_vals = &state.vals[state.base + a as usize..(state.base + a as usize + r_count as usize)];
                        debug!("{:?}", r_vals);
                        Vec::from(r_vals).into()
                    } else if b == 0 {
                        // return all values from R(A) to the ToS
                        let r_vals = &state.vals[state.base + a as usize..];
                        r_count = r_vals.len() as usize;
                        debug!("{:?}", r_vals);
                        Vec::from(r_vals).into()
                    } else {
                        unreachable!()
                    };
                    match state.callstack.last() {
                        Some(CallstackEntry(ret_clos, ReturnLocation::Interpreter(caller), frame, limit, ret, c)) => {
                            // We use the current closure, because we want to execute the vm RET
                            // instruction in it
                            state.clos = self.clos.clone();
                            debug!("returning to {:?}", unsafe { &(*ret_clos.ro(owner).prototype).source });
                            state.pc = pc;
                            return state
                        },
                        Some(&CallstackEntry(ref ret_clos, ReturnLocation::Generator(block, disp), frame, limit, ret, c)) => {
                            state.clos = ret_clos.clone();
                            self.set_current(ret_clos.clone());
                            state.base = frame;
                            debug!("returning {c}");
                            if c == 1 {
                                // No values are saved
                                state.vals.truncate(limit);
                            } else if c >= 2 {
                                // (C-1) values are saved
                                let parent_stack = unsafe { (*state.clos.ro(owner).prototype).max_stack as usize };
                                //vals.extend_from_slice(r_vals.as_slice());
                                for i in 0..=(c - 2) {
                                    debug!("huh {}", i);
                                    // Only copy the correct number of arguments from the CALL
                                    state.vals[ret + i as usize] = r_vals[i as usize].clone();
                                }
                                //assert!(limit >= ret + c as usize - 1);
                                state.vals.truncate(limit);
                                //state.vals.truncate(ret + c as usize - 1);
                            } else {
                                // Multiple return results are saved
                                for (i, v) in r_vals.drain(..).enumerate() {
                                    // Only copy the correct number of arguments from the CALL
                                    state.vals[ret + i] = v;
                                }
                                debug!("{:?} {}", &state.vals, r_count);
                                state.vals.truncate(ret + r_count);
                            }
                            id = block;
                            off = disp;
                            state.vals.truncate(limit);
                            debug!("after generator return, {:?}", &state.vals[state.base..]);
                            state.callstack.pop();
                        },
                        x => unimplemented!("{:?}", x),
                    }
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
