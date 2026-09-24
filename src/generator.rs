#![allow(unused_variables, unused_assignments, unused)]

use std::borrow::Cow;
use std::collections::HashMap;
use std::ops::{Coroutine, CoroutineState, Deref};
use std::pin::Pin;
use std::rc::Rc;
use std::cell::{Cell, RefCell};

use crate::vm::{CallstackEntry, HashWitness, NClosure, NativeFunc, Opcode, ReturnLocation, Upvalue};
use qcell::{LCell, LCellOwner};
use crate::Owner;
use crate::vm::{Tc, Vm};
use crate::vm::{BlockId, HashRef};
use crate::vm::{LClosure, LProto};
use crate::vm::{LValue, LType, Number, Table, FVec, LBoxed, LCanon, IStr};
use crate::vm::{InstructionDecode, Unpacker};
use crate::vm::RunState;
use crate::vm::LConstant;
use crate::vm::InternedHasher;
use crate::chunk::Constant;
use crate::chunk::Instruction;
use crate::window::{windowed, Access, Window};
// The native code generator (`JitContext`) and its per-block `JitInfo` (dynasm
// buffer + hotness tiering) are only needed with the `jit` feature. LBBV on its
// own is a second interpreter tier and doesn't touch them.
#[cfg(feature = "jit")]
use crate::jit::{JitInfo, JitContext};
use crate::gc::{Mark, Heap, GcCtx};

use crate::{debug, info, warn};
use smallvec::SmallVec;

impl<'src, 'intern> LValue<'src, 'intern> {
    /// Get the LType of an observed value
    pub fn typeof_(&self) -> LType {
        match self {
            LValue::Number(_) => LType::Number,
            LValue::InternedString(_) | LValue::OwnedString(_) => LType::String,
            LValue::Table(t) => LType::Table,
            LValue::LClosure(_) | LValue::NClosure(_) => LType::Closure,
            LValue::Nil => LType::Nil,
            LValue::Bool(_) => LType::Bool,
            _ => LType::Unknown,
        }
    }

    /// Get the CType of an observed value: this may have more precise information, such as
    /// specialized call targets for functions.
    pub fn ctypeof_(&self) -> CType {
        match self {
            LValue::NClosure(c) => CType::NativeFunction(c.clone()),
            // Safety: Ok this one is kinda sketchy. We only use CTypes inside Specializer, which
            // is parameterized over the same pre-transmute lifetimes and thus outlives them.
            LValue::LClosure(c) => CType::LuaFunction(unsafe { core::mem::transmute(c.clone()) }),
            x => CType::Type(x.typeof_()),
        }

    }
}

#[derive(Debug)]
pub struct Block {
    pub instructions: Vec<Residual>,
    /// The bytecode PC the block starts at, or the PC of the instruction a
    /// block starting inside one belongs to.
    pub pc: Pc,
    /// Whether the block may have allocated since its last GC safepoint, which
    /// it then gets at its end. See Note [Block safepoints].
    allocates: bool,
    /// A version of a pc's context, which jumps to it enter. See Note [Version
    /// compatibility].
    context: Option<Rc<Context>>,
    #[cfg(feature = "jit")]
    pub jit_info: JitInfo,
    /// Times the interpreter entered the block, shown by `dump`.
    #[cfg(feature = "graph")]
    pub entered: u64,
}

// Note [Block safepoints]
// ~~~~~~~~~~~~~~~~~~~~~~~
// The collector steps only at safepoints (`Residual::GC`), so any code that
// allocates must reach one, or a loop allocating only there never collects.
// Emitters say an operation allocates with `YieldOp::CollectGarbage`, and a
// call that may reach a native may allocate too (a call to a Lua function
// doesn't: its own blocks have safepoints); either marks its block, which gets one
// safepoint just before the residual ending it (a jump, a select, a thunk, a
// return). One per block, not per allocation: each safepoint flushes the JIT's
// register window, and a block's allocations are few enough to wait for its end.

impl Block {
    fn new(pc: Pc) -> Self {
        Self {
            instructions: vec![],
            pc,
            allocates: false,
            context: None,
            #[cfg(feature = "jit")]
            jit_info: JitInfo::new(),
            #[cfg(feature = "graph")]
            entered: 0,
        }
    }
}

#[cfg(feature = "unreachable")]
#[macro_export]
macro_rules! unreachable {
    () => { unsafe { core::hint::unreachable_unchecked() } }
}

macro_rules! define_exec {
    ($name:ident, [$($cap:ident: $cap_ty:ty),*], [$($const_param:ident: $const_ty:ty),*], |$owner:ident, $state:ident, $($args:ident),*| $body:block) => {
        #[derive(Clone)]
        pub struct $name<$(const $const_param: $const_ty),*> {
            $(pub $cap: $cap_ty),*
        }

        impl<$(const $const_param: $const_ty),*> FnOnce<(&mut Owner, &mut RunState<'_, '_>)> for $name<$($const_param),*> {
            type Output = ();
            #[inline(always)]
            extern "rust-call" fn call_once(self, args: (&mut Owner, &mut RunState<'_, '_>)) {
                self.call(args)
            }
        }

        impl<$(const $const_param: $const_ty),*> FnMut<(&mut Owner, &mut RunState<'_, '_>)> for $name<$($const_param),*> {
            #[inline(always)]
            extern "rust-call" fn call_mut(&mut self, args: (&mut Owner, &mut RunState<'_, '_>)) {
                self.call(args)
            }
        }

        impl<$(const $const_param: $const_ty),*> Fn<(&mut Owner, &mut RunState<'_, '_>)> for $name<$($const_param),*> {
            #[inline(always)]
            extern "rust-call" fn call(&self, (owner, state): (&mut Owner, &mut RunState<'_, '_>)) {
                let $name { $($cap),* } = self;
                $(let $args = *$cap;)*
                let $owner = owner;
                let $state = state;
                $body
            }
        }
    };
}

/// The arithmetic opcode's `[OP: Opcode, $params]` instance of a `windowed!`
/// op, constructed with `new($args)`.
macro_rules! dispatch_numeric_window {
    ($opcode:expr, $name:ident, [$($p:expr),*], ($($arg:expr),*)) => {
        match $opcode {
            Opcode::ADD => Rc::new($name::<{Opcode::ADD} $(, {$p})*>::new($($arg),*)) as Rc<dyn Window>,
            Opcode::SUB => Rc::new($name::<{Opcode::SUB} $(, {$p})*>::new($($arg),*)),
            Opcode::MUL => Rc::new($name::<{Opcode::MUL} $(, {$p})*>::new($($arg),*)),
            Opcode::DIV => Rc::new($name::<{Opcode::DIV} $(, {$p})*>::new($($arg),*)),
            Opcode::MOD => Rc::new($name::<{Opcode::MOD} $(, {$p})*>::new($($arg),*)),
            Opcode::POW => Rc::new($name::<{Opcode::POW} $(, {$p})*>::new($($arg),*)),
            _ => unreachable!(),
        }
    };
}

/// `dispatch_numeric_window`, for the integer ops. See Note [Integers].
macro_rules! dispatch_integer_window {
    ($opcode:expr, $name:ident, ($($arg:expr),*)) => {
        match $opcode {
            Opcode::ADD => Rc::new($name::<{Opcode::ADD}>::new($($arg),*)) as Rc<dyn Window>,
            Opcode::SUB => Rc::new($name::<{Opcode::SUB}>::new($($arg),*)),
            Opcode::MUL => Rc::new($name::<{Opcode::MUL}>::new($($arg),*)),
            Opcode::MOD => Rc::new($name::<{Opcode::MOD}>::new($($arg),*)),
            _ => unreachable!(),
        }
    };
}

macro_rules! dispatch_compare_window {
    ($opcode:expr, $name:ident, [$($p:expr),*], ($($arg:expr),*)) => {
        match $opcode {
            Opcode::EQ => Rc::new($name::<{Opcode::EQ} $(, {$p})*>::new($($arg),*)) as Rc<dyn Window>,
            Opcode::LT => Rc::new($name::<{Opcode::LT} $(, {$p})*>::new($($arg),*)),
            Opcode::LE => Rc::new($name::<{Opcode::LE} $(, {$p})*>::new($($arg),*)),
            _ => unreachable!(),
        }
    };
}

/// In a generator, the types of an op's two operands, as `TypeofRk` gives
/// them, for an op computing on integers: with one an integer, whether an
/// unknown other is one is found out (`DiscoverInteger`). See Note [Integers].
///
/// The other register is guarded even when its type is known, statically, so
/// that a way into the op already holding both integers takes the same guard
/// as one finding out: the subblocks after the guard are shared by its outcome
/// and the context, which are then the same, so the op must be at the same
/// point in each.
macro_rules! discover_integers {
    ($lhs:expr, $rhs:expr) => {{
        let integer = ResumeArg::Type(CType::Integer);
        let mut lt = yield YieldOp::TypeofRk($lhs);
        let mut rt = yield YieldOp::TypeofRk($rhs);
        if lt == integer && ($rhs & 0x100) == 0 {
            if (yield YieldOp::DiscoverInteger($rhs)) == ResumeArg::Matched {
                rt = integer.clone();
            }
        } else if rt == integer && ($lhs & 0x100) == 0 {
            if (yield YieldOp::DiscoverInteger($lhs)) == ResumeArg::Matched {
                lt = integer.clone();
            }
        }
        (lt, rt)
    }};
}


#[derive(Debug)]
pub enum ExecEffect {
    Jump(BlockId),
    Call(usize, usize, u16),
}
#[derive(Clone)]
pub struct ResidualExec {
    pub name: &'static str,
    pub body: Rc<dyn for <'a, 'b, 'src, 'intern> Fn(&mut Owner, &'b mut RunState<'src, 'intern>)>,
    pub template: Option<Rc<dyn Fn()->()>>,
}

/// A residual as the graph and window dumps label it.
impl std::fmt::Display for Residual {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Residual::Guard { idx, expected } => write!(f, "guard({}, {})", idx, expected),
            Residual::NativeGuard { idx, ptr } => write!(f, "native_guard({}, {:p})", idx, *ptr),
            Residual::LuaGuard { idx, ptr } => write!(f, "lua_guard({}, {:p})", idx, *ptr),
            Residual::Exec(ResidualExec { name, .. }) => write!(f, "exec({})", name),
            Residual::ExecWindow(w) => write!(f, "window({})", window_label(&**w)),
            Residual::GuardDynamic(w) => write!(f, "guard_dynamic({})", window_label(&**w)),
            Residual::Jump(target) => write!(f, "jump({})", target.0),
            Residual::Call { a, b, c } => write!(f, "call({}, {}, {})", a, b, c),
            Residual::NativeCall { nf, a, b, c } => write!(f, "ncall({:p}, {}, {}, {})", nf, a, b, c),
            Residual::LuaCall { lclos, a, b, c } => write!(f, "lcall({:p}, {}, {}, {})", lclos, a, b, c),
            Residual::HashGuard { tab, href, expected } => write!(f, "hguard({}, {:?}, {})", tab, href, expected),
            Residual::EpochCheck { tab, href } => write!(f, "epoch({}, {:?})", tab, href),
            Residual::Thunk(_) => write!(f, "thunk"),
            Residual::Select(targets) => write!(f, "select"),
            Residual::Ret(_, _, _) => write!(f, "ret"),
            Residual::GC => write!(f, "gc"),
        }
    }
}

/// A window op and its operands, as the dumps label it.
fn window_label(w: &dyn Window) -> String {
    let operands = w.operands().iter().zip(w.accesses()).map(|(slot, access)| match access {
        Access::Read => format!(", {slot}"),
        Access::Write => format!(", out {slot}"),
        Access::Update => format!(", inout {slot}"),
    });
    format!("{}{}", w.name(), operands.collect::<String>())
}

impl ResidualExec {
    pub fn new(name: &'static str, body: Rc<dyn for <'a, 'b, 'src, 'intern> Fn(&mut Owner, &'b mut RunState<'src, 'intern>)>) -> Self {
        Self { name, body, template: None }
    }
}

impl std::fmt::Debug for ResidualExec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "exec({}, {:p})", self.name, self.body.as_ref() as &_ as *const _ as *const ())
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
    TypeofRk(usize), // Resumed with the type of STACK[idx] or CONSTANT[idx]
    Guard(usize, LType), // Resumed with either Matched or Failed if STACK[idx] is the expected
                         // type
    GuardRk(usize, LType), // Resumed with either Matched or Failed if STACK[idx] or CONSTANT[idx]
                           // is the expected type
    GuardCType(usize, CType), // GuardRk, for a CType no LType guard tells apart: Integer.
                              // See Note [Integers]
    DiscoverInteger(usize), // Which of the number sublattice STACK[idx] is in: Integer, or a
                            // number, statically, or as GuardCType(idx, Integer) finds out if
                            // unknown. See Note [Integers]
    TypeofK(usize), // Resumed with the type of CONSTANT[idx], for an index too wide for an rk
    IntegerK(usize), // Resumed with the value of CONSTANT[idx], a `CType::Integer`
    Demote(std::ops::Range<usize>), // Lower the integers in STACK[range] to doubles, for code
                                    // reading them as any value. See Note [Integers]
    GuardDynamic(Rc<dyn Window>), // Resumed with Matched or Failed as the test op passes or fails.
                                  // See Note [Dynamic guards]
    Exec(ResidualExec), // Emit a residual operation that will be executed
    ExecWindow(Rc<dyn Window>), // Emit a copy&patch window op. See Note [Register window].
    SetTypes(Vec<(usize, LType)>), // Inform the executor that STACK[idx] = type for each entry
    SetCTypes(Vec<(usize, CType)>), // Inform the executor that STACK[idx] = type for each entry
    Jump(BlockId), // Emit a jump to the given BlockId
    Select(Vec<(&'static str, BlockId)>), // Emit a jump to one of several branches, based on
                                      // `state.select` at runtime
    GetBlock(Pc), // Resumed with the BlockId for calling the given PC with the current types
    Call(CallTarget), // Call a block target. Probably need a ResumeArg for returned values later.

    HashKey(usize, usize), // Looks up or allocates an HREF for STACK[idx][key], if key is
    TryHashKey(usize, usize), // Looks up but does not allocate an HREF..
    UpdateHashRef(HashRef, CType), // Update the type of HREF to a new type
    SetHazards(Option<usize>, Option<HashRef>), // Set optimization hazards, potentially
                                        // scoped to only information that may alias with an href,
                                        // and potentially keeping information about a specific
                                        // stack slot intact.
    CollectGarbage,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HashKey<'src, 'intern> {
    /// The HashRef
    pub idx: usize,
    pub key: LConstant<'src, 'intern>,
    pub known_type: CType,
    /// Optimization hazards: if set to `true` for an index, index is already checked
    /// for aliasing and an epoch check can be elided.
    pub hazards: SmallVec<[bool; 8]>,
}

impl<'src, 'intern> HashKey<'src, 'intern> {
    fn tostring(&self, owner: &Owner) -> String {
        let lv: LValue = (&self.key).into();
        format!("hkey({}, {})",
            String::from_utf8_lossy(lv.as_string_nolock().unwrap().as_slice()).to_owned().replace("\0",""),
            self.known_type)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ResumeArg {
    Start,
    Matched,
    MatchedConst(usize),
    Failed,
    Type(CType),
    BlockId(BlockId),
    HashRef(HashRef, CType),
    Integer(i32),
}

pub fn emit_loadk(bx: u32, c: LType, dest: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        // One op per constant kind: converting any constant is a `match` on its
        // kind, which compiles to a jump table the copier can't copy.
        windowed!(LoadKNumber, [index: u32], [], |owner, state, base| (out dest) {
            let Constant::Number(n) = &(&(*state.clos.ro(owner).prototype).constants.items)[index as usize] else { unreachable!() };
            *dest = LBoxed::from_number(n.0);
        });
        windowed!(LoadKInteger, [value: i32], [], |owner, state, base| (out dest) {
            *dest = LBoxed::from_int(value);
        });
        windowed!(LoadKString, [index: u32], [], |owner, state, base| (out dest) {
            let Constant::String(s) = &(&(*state.clos.ro(owner).prototype).constants.items)[index as usize] else { unreachable!() };
            *dest = LBoxed::interned(*s);
        });
        match c {
            LType::Number => {
                let ResumeArg::Type(t) = (yield YieldOp::TypeofK(bx as usize)) else { unreachable!() };
                if t == CType::Integer {
                    let ResumeArg::Integer(value) = (yield YieldOp::IntegerK(bx as usize)) else { unreachable!() };
                    yield YieldOp::ExecWindow(Rc::new(LoadKInteger::new(value, &[dest])));
                } else {
                    yield YieldOp::ExecWindow(Rc::new(LoadKNumber::new(bx, &[dest])));
                }
                yield YieldOp::SetCTypes(vec![(dest, t)]);
            },
            LType::String => {
                yield YieldOp::ExecWindow(Rc::new(LoadKString::new(bx, &[dest])));
                yield YieldOp::SetTypes(vec![(dest, LType::String)]);
            },
            _ => unreachable!(),
        }
        return arg;
    }
}

/// `R(A) := (Bool)B; if (C) pc++`, `pc` being the next instruction's.
pub fn emit_loadbool(dest: usize, value: bool, skip: bool, pc: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        windowed!(LoadBool, [value: u8], [], |owner, state, base| (out dest) {
            *dest = LBoxed::from_bool(value != 0);
        });
        yield YieldOp::ExecWindow(Rc::new(LoadBool::new(value as u8, &[dest])));
        yield YieldOp::SetTypes(vec![(dest, LType::Bool)]);
        if skip {
            arg = yield YieldOp::GetBlock(pc + 1);
            let ResumeArg::BlockId(target) = arg else { unreachable!() };
            arg = yield YieldOp::Jump(target);
        }
        arg
    }
}

/// `R(A) := ... := R(B) := nil`.
pub fn emit_loadnil(a: usize, b: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        windowed!(LoadNil, [], [], |owner, state, base| (out dest) {
            *dest = LBoxed::NIL;
        });
        for dest in a..=b {
            yield YieldOp::ExecWindow(Rc::new(LoadNil::new(&[dest])));
        }
        yield YieldOp::SetTypes((a..=b).map(|dest| (dest, LType::Nil)).collect());
        arg
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
        yield YieldOp::Exec(ResidualExec::new("getglobal", Rc::new(move |owner, state| {
            state.vals[state.base + dest as usize] = state._G.get(owner, &(&kst).into(), state.intern).unwrap_or((&Constant::Nil).into());
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
        yield YieldOp::Demote(dest..dest + 1);
        yield YieldOp::Exec(ResidualExec::new("setglobal", Rc::new(move |owner, state| {
            state._G.set(owner, (&kst).into(), state.vals[state.base + dest as usize], state.intern);
        })));
        arg
    }
}

pub fn emit_gettable(a: usize, b: usize, c: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Guard(b, LType::Table);
        if arg != ResumeArg::Matched {
            let have = yield YieldOp::Typeof(b);
            arg = yield YieldOp::Exec(ResidualExec::new("gettable_meta", Rc::new(move |owner, state| {
                panic!("gettable_meta {:?} {:?} {:?}", &state.vals, &state.vals[state.base + b], have)
            })));
            yield YieldOp::SetTypes(vec![(a, LType::Unknown)]);
            return arg;
        }
        // Object shape specialization
        arg = yield YieldOp::HashKey(b, c);
        if let ResumeArg::HashRef(hc, htype) = arg {
            windowed!(GetTableHref, [href: u8, key: usize], [], |owner, state, base| (table, out dest) {
                let witness = &state.hash_witnesses[state.witness_base + href as usize];
                debug!("gettable_href with {:?}", &witness);
                let LValue::Table(tab) = table.unbox() else { unreachable!() };
                #[cfg(debug_assertions)]
                let witness = witness.as_ref().unwrap();
                #[cfg(not(debug_assertions))]
                let witness = witness.as_ref().unwrap_unchecked();
                let (k, val1) = tab.ro(owner).hash.get_index(witness.index).unwrap();

                // Sanity check
                // Move this into make_href_check since we need it attached to the HashKey instead
                #[cfg(debug_assertions)]
                {
                    let val2 = tab.ro(owner).hash.get(&LCanon::new((&witness.key).into(), state.intern)).copied().unwrap();
                    let full_key = Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, key as u16);
                    debug!("{:?}", &tab.ro(owner));
                    let Ok(const_key) = full_key else { unreachable!() };
                    assert_eq!(*k, LCanon::new(LBoxed::from(const_key), state.intern));
                    assert_eq!(val1.bits(), val2.bits());
                }

                debug!("gettable_href fetched {val1:?}");
                *dest = *val1;
            });
            arg = yield YieldOp::ExecWindow(Rc::new(GetTableHref::new(hc.0, c, &[b, a])));
            yield YieldOp::SetCTypes(vec![(a, htype.clone())]);
        } else {
            // An integer key in the array part, in a register or a constant (its
            // value, `k`): the array slot. See Note [Dynamic guards].
            let integer = match yield YieldOp::GuardCType(c, CType::Integer) {
                ResumeArg::MatchedConst(k) => {
                    let ResumeArg::Integer(k) = (yield YieldOp::IntegerK(k)) else { unreachable!() };
                    Some(Some(k))
                },
                ResumeArg::Matched => Some(None),
                _ => None,
            };
            let in_array = match integer {
                Some(Some(k)) => yield YieldOp::GuardDynamic(Rc::new(InArrayK::new(k, &[b]))),
                Some(None) => yield YieldOp::GuardDynamic(Rc::new(InArray::new(&[b, c]))),
                None => ResumeArg::Failed,
            };
            if let (Some(Some(k)), ResumeArg::Matched) = (integer, &in_array) {
                windowed!(GetTableArray, [k: i32], [], |owner, state, base| (table, out dest) {
                    let LValue::Table(tab) = table.unbox() else { core::hint::unreachable_unchecked() };
                    *dest = *tab.ro(owner).array.get_unchecked(integer_slot(k));
                });
                arg = yield YieldOp::ExecWindow(Rc::new(GetTableArray::new(k, &[b, a])));
            } else if let (Some(None), ResumeArg::Matched) = (integer, &in_array) {
                windowed!(GetTableInteger, [], [], |owner, state, base| (table, key, out dest) {
                    let LValue::Table(tab) = table.unbox() else { core::hint::unreachable_unchecked() };
                    *dest = *tab.ro(owner).array.get_unchecked(integer_slot(key.as_int()));
                });
                arg = yield YieldOp::ExecWindow(Rc::new(GetTableInteger::new(&[b, c, a])));
            } else {
                // Any other key: through `gettable`.
                yield YieldOp::Demote(c..c + 1);
                arg = yield YieldOp::Exec(ResidualExec::new("gettable", Rc::new(move |owner, state| {
                    let kc = match Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, c as u16) {
                        Ok(c) => Cow::Owned(LValue::from(c)),
                        Err(lv) => Cow::Owned(lv.unbox()),
                    };
                    debug!("gettable {:?}", &kc);
                    let val_b = state.vals[state.base + b as usize].unbox();
                    state.vals[state.base + a as usize] = LBoxed::box_lvalue(val_b.gettable(owner, kc, state.intern));
                })));
            }
            yield YieldOp::SetTypes(vec![(a, LType::Unknown)]);
        }
        arg
    }
}

pub fn emit_settable(a: usize, b: usize, c: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Guard(a, LType::Table);
        if arg != ResumeArg::Matched {
            arg = yield YieldOp::Exec(ResidualExec::new("settable_meta", Rc::new(move |owner, state| {
                panic!("settable_meta {:?}", state.vals)
            })));
            arg = yield YieldOp::SetHazards(None, None);
            return arg;
        }
        // TODO: table shape specialization
        // An integer key in the array part, in a register or a constant (its
        // value, `k`), with the value in a register, stores into its slot. See
        // Note [Dynamic guards].
        let integer = match yield YieldOp::GuardCType(b, CType::Integer) {
            ResumeArg::MatchedConst(k) => {
                let ResumeArg::Integer(k) = (yield YieldOp::IntegerK(k)) else { unreachable!() };
                Some(Some(k))
            },
            ResumeArg::Matched => Some(None),
            _ => None,
        };
        let in_array = match (integer, c & 0x100) {
            (Some(Some(k)), 0) => yield YieldOp::GuardDynamic(Rc::new(InArrayK::new(k, &[a]))),
            (Some(None), 0) => yield YieldOp::GuardDynamic(Rc::new(InArray::new(&[a, b]))),
            _ => ResumeArg::Failed,
        };
        // A table holds a double. See Note [Integers].
        let int_value = in_array == ResumeArg::Matched && (yield YieldOp::TypeofRk(c)) == ResumeArg::Type(CType::Integer);
        if let (Some(Some(k)), ResumeArg::Matched) = (integer, &in_array) {
            windowed!(SetTableArray, [k: i32], [INT: bool], |owner, state, base| (table, value) {
                let LValue::Table(mut tab) = table.unbox() else { core::hint::unreachable_unchecked() };
                tab.barrier_back();
                *tab.rw(owner).array.get_unchecked_mut(integer_slot(k)) = double::<INT>(value);
            });
            arg = yield YieldOp::ExecWindow(if int_value {
                Rc::new(SetTableArray::<true>::new(k, &[a, c]))
            } else {
                Rc::new(SetTableArray::<false>::new(k, &[a, c]))
            });
        } else if let (Some(None), ResumeArg::Matched) = (integer, &in_array) {
            windowed!(SetTableInteger, [], [INT: bool], |owner, state, base| (table, key, value) {
                let LValue::Table(mut tab) = table.unbox() else { core::hint::unreachable_unchecked() };
                tab.barrier_back();
                *tab.rw(owner).array.get_unchecked_mut(integer_slot(key.as_int())) = double::<INT>(value);
            });
            arg = yield YieldOp::ExecWindow(if int_value {
                Rc::new(SetTableInteger::<true>::new(&[a, b, c]))
            } else {
                Rc::new(SetTableInteger::<false>::new(&[a, b, c]))
            });
        } else if let ResumeArg::Matched | ResumeArg::MatchedConst(_) = {
            yield YieldOp::Demote(b..b + 1);
            yield YieldOp::Demote(c..c + 1);
            yield YieldOp::GuardRk(b, LType::Number)
        } {
            // Any other number key, one past the array part, or a constant value:
            // through `set`.
            arg = yield YieldOp::Exec(ResidualExec::new("settable_array", Rc::new(move |owner, state| {
                let kb: LValue = match Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, b as u16) {
                    Ok(b) => LValue::from(b),
                    Err(lv) => lv.unbox(),
                };
                let LValue::Number(kb) = kb else { unreachable!() };
                let kc: LBoxed = match Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, c as u16) {
                    Ok(c) => LBoxed::from(c),
                    Err(lv) => *lv,
                };
                let LValue::Table(mut t) = state.vals[state.base + a].unbox() else { unreachable!() };
                t.set(owner, LBoxed::from_number(kb.0), kc, state.intern);
            })));
        } else {
            // Hash part set
            arg = ResumeArg::Failed;
            arg = yield YieldOp::TryHashKey(a, b);
            if let ResumeArg::HashRef(hb, htype) = arg {
                arg = yield YieldOp::TypeofRk(c);
                let mut mismatched_type = None;
                if let ResumeArg::Type(t) = arg {
                    // A table holds an integer constant as a double. See Note [Integers].
                    let t = if t == CType::Integer { CType::Type(LType::Number) } else { t };
                    if t != htype {
                        mismatched_type = Some(t);
                    } else {
                        // The value we're setting is statically known to be the same type as our
                        // hashkey, and so everything is fine
                    }
                } else {
                    mismatched_type = Some(CType::Type(LType::Unknown));
                }

                // Store through the witness; retyping the key's value moves the
                // table (and so the witness) to a new epoch.
                fn store<'src, 'intern>(owner: &mut Owner, state: &mut RunState<'src, 'intern>, table: LBoxed<'src, 'intern>, value: LBoxed<'src, 'intern>, href: u8, expected: LType, retype: bool) {
                    let hidx = state.witness_base + href as usize;
                    let witness = &state.hash_witnesses[hidx];
                    debug!("settable_href with {:?} {:?}", &witness, expected);
                    let LValue::Table(tab) = table.unbox() else { unreachable!() };
                    tab.barrier_back();
                    let (k, val1) = tab.rw(owner).hash.get_index_mut(witness.as_ref().unwrap().index).unwrap();
                    debug!("settable_href {:?} {:?}", &val1, expected);
                    #[cfg(debug_assertions)]
                    assert!(val1.unbox().typeof_() == expected);
                    *val1 = value;
                    if retype {
                        tab.rw(owner).epoch += 1;
                        // This is safe because we're statically updating the known type as well.
                        state.hash_witnesses[hidx].as_mut().unwrap().epoch = tab.rw(owner).epoch;
                    }
                }
                let expected = htype.as_ltype();
                let retype = mismatched_type.is_some();
                if c & 0x100 == 0 {
                    windowed!(SetTableHref, [href: u8, expected: LType], [RETYPE: bool], |owner, state, base| (table, value) {
                        store(owner, state, table, value, href, expected, RETYPE);
                    });
                    arg = yield YieldOp::ExecWindow(if retype {
                        Rc::new(SetTableHref::<true>::new(hb.0, expected, &[a, c]))
                    } else {
                        Rc::new(SetTableHref::<false>::new(hb.0, expected, &[a, c]))
                    });
                } else {
                    arg = yield YieldOp::Exec(ResidualExec::new("settable_href", Rc::new(move |owner, state| {
                        let table = state.vals[state.base + a];
                        let value: LBoxed = match Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, c as u16) {
                            Ok(c) => LBoxed::from(c),
                            Err(lv) => *lv,
                        };
                        store(owner, state, table, value, hb.0, expected, retype);
                    })));
                }
                if let Some(new_type) = mismatched_type {
                    // We statically know we will increment the epoch, so update the hashkey's
                    // known type. This also will set hazards.
                    arg = yield YieldOp::UpdateHashRef(hb, new_type);
                } else {
                    arg = yield YieldOp::SetHazards(Some(a), Some(hb));
                }
            } else {
                arg = yield YieldOp::Exec(ResidualExec::new("settable_hash", Rc::new(move |owner, state| {
                    let kb: LBoxed = match Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, b as u16) {
                        Ok(b) => LBoxed::from(b),
                        Err(lv) => *lv,
                    };
                    let kb = LCanon::new(kb, state.intern);
                    let kc: LBoxed = match Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, c as u16) {
                        Ok(c) => LBoxed::from(c),
                        Err(lv) => *lv,
                    };
                    let LValue::Table(t) = state.vals[state.base + a].unbox() else { unreachable!() };
                    t.barrier_back();
                    let kc_type = kc.unbox().typeof_();
                    if let Some(existing) = t.rw(owner).hash.insert(kb, kc) {
                        info!("settable_hash with existing key {:?} {:?}", &existing, kc);
                        if existing.unbox().typeof_() != kc_type {
                            t.rw(owner).epoch += 1;
                        }
                    } else {
                        // Set new key, which implies keys that previously chained through the
                        // metatable or resolved to nil are invalidated.
                        t.rw(owner).epoch += 1;
                    }
                })));
                arg = yield YieldOp::SetHazards(None, None);
            }
        }
        arg
    }
}

pub fn emit_newtable(a: usize, b: usize, c: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Exec(ResidualExec::new("newtable", Rc::new(move |owner, state| {
            // TODO: properly decode the "floating point byte" size hints instead
            state.vals[state.base + a as usize] = LBoxed::box_lvalue(LValue::Table(Tc::new(Table::new(b as usize, c as usize))));
        })));
        yield YieldOp::SetTypes(vec![(a, LType::Table)]);
        yield YieldOp::CollectGarbage;
        arg
    }
}

pub fn emit_setlist(a: usize, b: usize, c: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        // We don't need to guard on LType::Table, because this instruction is only ever used for
        // table initialization, which means it is definitely a table and doesn't e.g. have a
        // metatable we have to chain to.
        yield YieldOp::Demote(a + 1..if b == 0 { usize::MAX } else { a + 1 + b });
        arg = yield YieldOp::Exec(ResidualExec::new("setlist", Rc::new(move |owner, state| {
            match state.vals[state.base + a as usize].unbox() {
                LValue::Table(tab) => {
                    assert_ne!(c, 0);
                    tab.barrier_back();
                    let start = state.base + a as usize + 1;
                    let end = if b == 0 { state.top } else { start + b as usize };
                    let src = state.vals[start..end].iter().cloned();
                    tab.rw(owner).array.splice(
                        (c as usize-1)*50..,
                        src
                    ).for_each(drop);
                },
                _ => unreachable!(),
            };
        })));
        yield YieldOp::SetTypes(vec![(a, LType::Table)]);
        arg
    }
}

/// A numeric operand as a double, decoded from the integer encoding if `INT`.
/// See Note [Integers].
#[inline(always)]
unsafe fn number<'src, 'intern, const INT: bool>(v: LBoxed<'src, 'intern>) -> f64 {
    if INT {
        (unsafe { v.as_int() }) as f64
    } else {
        let Some(n) = v.as_number() else { unsafe { core::hint::unreachable_unchecked() } };
        n
    }
}

/// A value as a double, for a table to hold: re-encoded if `INT`. See Note
/// [Integers].
#[inline(always)]
unsafe fn double<'src, 'intern, const INT: bool>(v: LBoxed<'src, 'intern>) -> LBoxed<'src, 'intern> {
    if INT { LBoxed::from_number((unsafe { v.as_int() }) as f64) } else { v }
}

/// The integer op `OP`'s result, if it fits the integer encoding: it must be in
/// range, and neither -0 nor NaN. See Note [Integers].
#[inline(always)]
fn integer_op<const OP: Opcode>(l: i32, r: i32) -> Option<i32> {
    match OP {
        Opcode::ADD => l.checked_add(r),
        Opcode::SUB => l.checked_sub(r),
        // Zero times a negative number is -0.
        Opcode::MUL => l.checked_mul(r).filter(|&p| p != 0 || (l | r) >= 0),
        // Floored, as `lua_mod`. By zero, it is NaN.
        Opcode::MOD => (r != 0).then(|| {
            let m = l.wrapping_rem(r);
            if m != 0 && (m ^ r) < 0 { m + r } else { m }
        }),
        _ => unsafe { core::hint::unreachable_unchecked() },
    }
}

// The integer ops on registers and constants (`k`, their value), and their
// `GuardDynamic` tests that the result fits. See Note [Integers].
crate::window::windowed!(FitsRR, [], [OP: Opcode], |owner, state, base| (lhs, rhs) {
    state.select = integer_op::<OP>(lhs.as_int(), rhs.as_int()).is_none() as usize;
});
crate::window::windowed!(FitsKR, [k: i32], [OP: Opcode], |owner, state, base| (rhs) {
    state.select = integer_op::<OP>(k, rhs.as_int()).is_none() as usize;
});
crate::window::windowed!(FitsRK, [k: i32], [OP: Opcode], |owner, state, base| (lhs) {
    state.select = integer_op::<OP>(lhs.as_int(), k).is_none() as usize;
});
crate::window::windowed!(IntegerRR, [], [OP: Opcode], |owner, state, base| (lhs, rhs, out dest) {
    *dest = LBoxed::from_int(integer_op::<OP>(lhs.as_int(), rhs.as_int()).unwrap_unchecked());
});
crate::window::windowed!(IntegerKR, [k: i32], [OP: Opcode], |owner, state, base| (rhs, out dest) {
    *dest = LBoxed::from_int(integer_op::<OP>(k, rhs.as_int()).unwrap_unchecked());
});
crate::window::windowed!(IntegerRK, [k: i32], [OP: Opcode], |owner, state, base| (lhs, out dest) {
    *dest = LBoxed::from_int(integer_op::<OP>(lhs.as_int(), k).unwrap_unchecked());
});

// The double ops on registers, `LI`/`RI` if in the integer encoding, and
// constants (index `k`), read from the prototype. Unchecked, so that no panic
// path follows the stencil's `become` and the copy can slice it off.
crate::window::windowed!(NumericRR, [], [OP: Opcode, LI: bool, RI: bool], |owner, state, base| (lhs, rhs, out dest) {
    let (l, r) = (number::<LI>(lhs), number::<RI>(rhs));
    *dest = LBoxed::box_lvalue(LValue::Number(Number(l)).numeric_op(OP, &LValue::Number(Number(r))).unwrap());
});
crate::window::windowed!(NumericKK, [kl: u32, kr: u32], [OP: Opcode], |owner, state, base| (out dest) {
    let constants = &(&(*state.clos.ro(owner).prototype).constants.items);
    let Constant::Number(l) = &constants[kl as usize] else { core::hint::unreachable_unchecked() };
    let Constant::Number(r) = &constants[kr as usize] else { core::hint::unreachable_unchecked() };
    *dest = LBoxed::box_lvalue(LValue::Number(*l).numeric_op(OP, &LValue::Number(*r)).unwrap());
});
crate::window::windowed!(NumericKR, [k: u32], [OP: Opcode, RI: bool], |owner, state, base| (rhs, out dest) {
    let Constant::Number(l) = &(&(*state.clos.ro(owner).prototype).constants.items)[k as usize] else {
        core::hint::unreachable_unchecked()
    };
    *dest = LBoxed::box_lvalue(LValue::Number(*l).numeric_op(OP, &LValue::Number(Number(number::<RI>(rhs)))).unwrap());
});
crate::window::windowed!(NumericRK, [k: u32], [OP: Opcode, LI: bool], |owner, state, base| (lhs, out dest) {
    let Constant::Number(r) = &(&(*state.clos.ro(owner).prototype).constants.items)[k as usize] else {
        core::hint::unreachable_unchecked()
    };
    *dest = LBoxed::box_lvalue(LValue::Number(Number(number::<LI>(lhs))).numeric_op(OP, &LValue::Number(*r)).unwrap());
});

/// `NumericRR` for `opcode`, reading integer registers as `li`/`ri` say.
fn numeric_rr(opcode: Opcode, li: bool, ri: bool, operands: &[usize]) -> Rc<dyn Window> {
    match (li, ri) {
        (false, false) => dispatch_numeric_window!(opcode, NumericRR, [false, false], (operands)),
        (false, true) => dispatch_numeric_window!(opcode, NumericRR, [false, true], (operands)),
        (true, false) => dispatch_numeric_window!(opcode, NumericRR, [true, false], (operands)),
        (true, true) => dispatch_numeric_window!(opcode, NumericRR, [true, true], (operands)),
    }
}

/// `NumericKR` for `opcode`, reading an integer register if `ri`.
fn numeric_kr(opcode: Opcode, ri: bool, k: u32, operands: &[usize]) -> Rc<dyn Window> {
    match ri {
        false => dispatch_numeric_window!(opcode, NumericKR, [false], (k, operands)),
        true => dispatch_numeric_window!(opcode, NumericKR, [true], (k, operands)),
    }
}

/// `NumericRK` for `opcode`, reading an integer register if `li`.
fn numeric_rk(opcode: Opcode, li: bool, k: u32, operands: &[usize]) -> Rc<dyn Window> {
    match li {
        false => dispatch_numeric_window!(opcode, NumericRK, [false], (k, operands)),
        true => dispatch_numeric_window!(opcode, NumericRK, [true], (k, operands)),
    }
}

pub fn emit_numeric(opcode: Opcode, dest: usize, lhs: usize, rhs: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        let integer = ResumeArg::Type(CType::Integer);
        // --- Int Path --- See Note [Integers]. First, as finding out whether an
        // unknown operand is an integer finds out its type too.
        if matches!(opcode, Opcode::ADD | Opcode::SUB | Opcode::MUL | Opcode::MOD) {
            let (lt, rt) = discover_integers!(lhs, rhs);
            let (lk, rk) = ((lhs & 0x100) != 0, (rhs & 0x100) != 0);
            // A constant operand is its value, as `k`. luac folds two.
            let op = if lt != integer || rt != integer || (lk && rk) {
                None
            } else if lk {
                let ResumeArg::Integer(k) = (yield YieldOp::IntegerK(lhs & 0xff)) else { unreachable!() };
                Some((Some(dispatch_integer_window!(opcode, FitsKR, (k, &[rhs]))), dispatch_integer_window!(opcode, IntegerKR, (k, &[rhs, dest]))))
            } else if rk {
                let ResumeArg::Integer(k) = (yield YieldOp::IntegerK(rhs & 0xff)) else { unreachable!() };
                // Only MOD by a zero can fail with a constant divisor.
                let test = (opcode != Opcode::MOD || k == 0).then(|| dispatch_integer_window!(opcode, FitsRK, (k, &[lhs])));
                Some((test, dispatch_integer_window!(opcode, IntegerRK, (k, &[lhs, dest]))))
            } else {
                Some((Some(dispatch_integer_window!(opcode, FitsRR, (&[lhs, rhs]))), dispatch_integer_window!(opcode, IntegerRR, (&[lhs, rhs, dest]))))
            };
            if let Some((test, op)) = op {
                let fits = match test {
                    Some(test) => yield YieldOp::GuardDynamic(test),
                    None => ResumeArg::Matched,
                };
                if fits == ResumeArg::Matched {
                    yield YieldOp::ExecWindow(op);
                    yield YieldOp::SetCTypes(vec![(dest, CType::Integer)]);
                    return arg;
                }
            }
        }
        arg = yield YieldOp::GuardRk(lhs, LType::Table);
        if let ResumeArg::Matched | ResumeArg::MatchedConst(_) = arg {
            arg = yield YieldOp::GuardRk(rhs, LType::Table);
            if let ResumeArg::Matched | ResumeArg::MatchedConst(_) = arg {
                yield YieldOp::Exec(ResidualExec::new("numeric_table_table", Rc::new(move |owner, state| {
                    panic!();
                })));
                yield YieldOp::SetTypes(vec![(dest, LType::Unknown)]);
                return arg;
            }
        }
        // --- Number Path ---
        // An integer register is decoded, not lowered. See Note [Integers].
        let lint = (lhs & 0x100) == 0 && (yield YieldOp::TypeofRk(lhs)) == integer;
        let rint = (rhs & 0x100) == 0 && (yield YieldOp::TypeofRk(rhs)) == integer;
        let larg = if lint { ResumeArg::Matched } else { yield YieldOp::GuardRk(lhs, LType::Number) };
        let rarg = if rint { ResumeArg::Matched } else { yield YieldOp::GuardRk(rhs, LType::Number) };
        let window = match (larg, rarg) {
            (ResumeArg::Matched, ResumeArg::Matched) => Some(numeric_rr(opcode, lint, rint, &[lhs, rhs, dest])),
            (ResumeArg::MatchedConst(lhsc), ResumeArg::MatchedConst(rhsc)) => {
                Some(dispatch_numeric_window!(opcode, NumericKK, [], (lhsc as u32, rhsc as u32, &[dest])))
            },
            (ResumeArg::MatchedConst(lhsc), ResumeArg::Matched) => Some(numeric_kr(opcode, rint, lhsc as u32, &[rhs, dest])),
            (ResumeArg::Matched, ResumeArg::MatchedConst(rhsc)) => Some(numeric_rk(opcode, lint, rhsc as u32, &[lhs, dest])),
            _ => None,
        };
        if let Some(window) = window {
            yield YieldOp::ExecWindow(window);
            yield YieldOp::SetTypes(vec![(dest, LType::Number)]);
            return arg;
        }

        // --- Str Path ---
        arg = yield YieldOp::GuardRk(lhs, LType::String);
        if let ResumeArg::Matched | ResumeArg::MatchedConst(_) = arg {
            arg = yield YieldOp::GuardRk(rhs, LType::String);
            if let ResumeArg::Matched | ResumeArg::MatchedConst(_) = arg {
                yield YieldOp::Exec(ResidualExec::new("numeric_str_str", Rc::new(move |owner, state| {
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
        //panic!("Type mismatch trap");
        arg = yield YieldOp::Typeof(lhs);
        arg = yield YieldOp::Exec(ResidualExec::new("numeric_fail", Rc::new(move |owner, state| {
            panic!("numeric runtime type mismatch {:?} {:?}", arg, state.vals)
        })));
        arg
    }
}

/// Set `select` for a compare's select: 0 to take the jump, when the condition
/// isn't `a`. `OP` is a const param, so each stencil compares one way.
/// Unchecked, so that no panic path follows the stencil's `become`.
#[inline(always)]
unsafe fn select<const OP: Opcode, T: PartialOrd>(state: &mut RunState, a: u8, l: T, r: T) {
    let cond = match OP {
        Opcode::EQ => l == r,
        Opcode::LT => l < r,
        Opcode::LE => l <= r,
        _ => unsafe { core::hint::unreachable_unchecked() },
    };
    state.select = if (cond as u8) != a { 0 } else { 1 };
}

// Compares of integers, a constant one as `k`, its value. See Note [Integers].
crate::window::windowed!(CompareIntRR, [a: u8], [OP: Opcode], |owner, state, base| (lhs, rhs) {
    select::<OP, i32>(state, a, lhs.as_int(), rhs.as_int());
});
crate::window::windowed!(CompareIntKR, [a: u8, k: i32], [OP: Opcode], |owner, state, base| (rhs) {
    select::<OP, i32>(state, a, k, rhs.as_int());
});
crate::window::windowed!(CompareIntRK, [a: u8, k: i32], [OP: Opcode], |owner, state, base| (lhs) {
    select::<OP, i32>(state, a, lhs.as_int(), k);
});

// Compares of numbers: registers, `LI`/`RI` if in the integer encoding, and a
// constant, `k` its index, read from the prototype.
crate::window::windowed!(CompareRR, [a: u8], [OP: Opcode, LI: bool, RI: bool], |owner, state, base| (lhs, rhs) {
    select::<OP, f64>(state, a, number::<LI>(lhs), number::<RI>(rhs));
});
crate::window::windowed!(CompareKR, [a: u8, k: u32], [OP: Opcode, RI: bool], |owner, state, base| (rhs) {
    let Constant::Number(l) = &(&(*state.clos.ro(owner).prototype).constants.items)[k as usize] else {
        core::hint::unreachable_unchecked()
    };
    select::<OP, f64>(state, a, l.0, number::<RI>(rhs));
});
crate::window::windowed!(CompareRK, [a: u8, k: u32], [OP: Opcode, LI: bool], |owner, state, base| (lhs) {
    let Constant::Number(r) = &(&(*state.clos.ro(owner).prototype).constants.items)[k as usize] else {
        core::hint::unreachable_unchecked()
    };
    select::<OP, f64>(state, a, number::<LI>(lhs), r.0);
});

/// `CompareRR` for `opcode`, reading integer registers as `li`/`ri` say.
fn compare_rr(opcode: Opcode, li: bool, ri: bool, a: u8, operands: &[usize]) -> Rc<dyn Window> {
    match (li, ri) {
        (false, false) => dispatch_compare_window!(opcode, CompareRR, [false, false], (a, operands)),
        (false, true) => dispatch_compare_window!(opcode, CompareRR, [false, true], (a, operands)),
        (true, false) => dispatch_compare_window!(opcode, CompareRR, [true, false], (a, operands)),
        (true, true) => dispatch_compare_window!(opcode, CompareRR, [true, true], (a, operands)),
    }
}

/// `CompareKR` for `opcode`, reading an integer register if `ri`.
fn compare_kr(opcode: Opcode, ri: bool, a: u8, k: u32, operands: &[usize]) -> Rc<dyn Window> {
    match ri {
        false => dispatch_compare_window!(opcode, CompareKR, [false], (a, k, operands)),
        true => dispatch_compare_window!(opcode, CompareKR, [true], (a, k, operands)),
    }
}

/// `CompareRK` for `opcode`, reading an integer register if `li`.
fn compare_rk(opcode: Opcode, li: bool, a: u8, k: u32, operands: &[usize]) -> Rc<dyn Window> {
    match li {
        false => dispatch_compare_window!(opcode, CompareRK, [false], (a, k, operands)),
        true => dispatch_compare_window!(opcode, CompareRK, [true], (a, k, operands)),
    }
}

pub fn emit_compare(opcode: Opcode, a: u8, b: usize, c: usize, pc: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        // Integers compare as integers, and an integer register is decoded, not
        // lowered. See Note [Integers].
        let integer = ResumeArg::Type(CType::Integer);
        let (lt, rt) = discover_integers!(b, c);
        let integers = lt == integer && rt == integer;
        let lint = (b & 0x100) == 0 && lt == integer;
        let rint = (c & 0x100) == 0 && rt == integer;
        let larg = if lint { ResumeArg::Matched } else { yield YieldOp::GuardRk(b, LType::Number) };
        let rarg = if rint { ResumeArg::Matched } else { yield YieldOp::GuardRk(c, LType::Number) };

        let lnil = yield YieldOp::GuardRk(b, LType::Nil);
        let rnil = yield YieldOp::GuardRk(c, LType::Nil);

        arg = yield YieldOp::GetBlock(pc);
        let ResumeArg::BlockId(fallthrough) = arg else { unreachable!() };
        arg = yield YieldOp::GetBlock((pc as isize + 1 as isize) as usize);
        let ResumeArg::BlockId(taken) = arg else { unreachable!() };

        match (larg, rarg) {
            (ResumeArg::Matched, ResumeArg::Matched) if integers => {
                arg = yield YieldOp::ExecWindow(dispatch_compare_window!(opcode, CompareIntRR, [], (a, &[b, c])));
            },
            (ResumeArg::Matched, ResumeArg::Matched) => {
                arg = yield YieldOp::ExecWindow(compare_rr(opcode, lint, rint, a, &[b, c]));
            },
            (ResumeArg::MatchedConst(rb), ResumeArg::Matched) if integers => {
                let ResumeArg::Integer(k) = (yield YieldOp::IntegerK(rb)) else { unreachable!() };
                arg = yield YieldOp::ExecWindow(dispatch_compare_window!(opcode, CompareIntKR, [], (a, k, &[c])));
            },
            (ResumeArg::MatchedConst(rb), ResumeArg::Matched) => {
                arg = yield YieldOp::ExecWindow(compare_kr(opcode, rint, a, rb as u32, &[c]));
            },
            (ResumeArg::Matched, ResumeArg::MatchedConst(rc)) if integers => {
                let ResumeArg::Integer(k) = (yield YieldOp::IntegerK(rc)) else { unreachable!() };
                arg = yield YieldOp::ExecWindow(dispatch_compare_window!(opcode, CompareIntRK, [], (a, k, &[b])));
            },
            (ResumeArg::Matched, ResumeArg::MatchedConst(rc)) => {
                arg = yield YieldOp::ExecWindow(compare_rk(opcode, lint, a, rc as u32, &[b]));
            },
            (ResumeArg::MatchedConst(rb), ResumeArg::MatchedConst(rc)) => {
                unimplemented!()
            },
            (larg, rarg) => {
                if opcode != Opcode::EQ {
                    unimplemented!("ordering a nil (an error, or a metamethod)");
                }
                let equal = match (&lnil, &rnil) {
                    (ResumeArg::Matched | ResumeArg::MatchedConst(_), ResumeArg::Matched | ResumeArg::MatchedConst(_)) => true,
                    (ResumeArg::Matched | ResumeArg::MatchedConst(_), _) | (_, ResumeArg::Matched | ResumeArg::MatchedConst(_)) => false,
                    _ => unimplemented!(),
                };
                // Statically decided: take the jump when the condition isn't `a`,
                // as `select` does.
                yield YieldOp::Jump(if (equal as u8) != a { taken } else { fallthrough });
            }
        }
        arg = yield YieldOp::Select(vec![("taken", taken), ("fallthrough", fallthrough)]);
        arg
    }
}

pub fn emit_test(a: usize, c: u16, pc: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        // TODO: __eq metatable?
        arg = yield YieldOp::GetBlock(pc);
        let ResumeArg::BlockId(fallthrough) = arg else { unreachable!() };
        arg = yield YieldOp::GetBlock((pc as isize + 1 as isize) as usize);
        let ResumeArg::BlockId(taken) = arg else { unreachable!() };

        arg = yield YieldOp::Guard(a, LType::Bool);
        if let ResumeArg::Matched = arg {
            arg = yield YieldOp::Exec(ResidualExec::new("test_bool", Rc::new(move |owner, state| {
                let LValue::Bool(b) = state.vals[state.base + a as usize].unbox() else { unreachable!() };
                state.select = (b as u16 == c) as usize;
            })));
            arg = yield YieldOp::Select(vec![("taken", taken), ("fallthrough", fallthrough)]);
            return arg
        }
        // The next instruction (a jump) runs when R(A)'s truthiness is C, else it
        // is skipped. Nil is false.
        arg = yield YieldOp::Guard(a, LType::Nil);
        if let ResumeArg::Matched = arg {
            arg = yield YieldOp::Jump(if c == 0 { fallthrough } else { taken });
            return arg;
        }
        // Everything else is true.
        arg = yield YieldOp::Jump(if c != 0 { fallthrough } else { taken });
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
        arg = yield YieldOp::Exec(ResidualExec::new("unm", Rc::new(move |owner, state| {
            let res = match state.vals[state.base + b as usize].unbox() {
                // TODO: metatables
                LValue::Number(n) => LValue::Number(Number(-n.0)),
                _ => unimplemented!(),
            };
            state.vals[state.base + a as usize] = LBoxed::box_lvalue(res);
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
            arg = yield YieldOp::Exec(ResidualExec::new("len_str", Rc::new(move |owner, state| {
                let n = match state.vals[state.base + b].unbox() {
                    LValue::OwnedString(s) => s.as_slice().len(),
                    LValue::InternedString(s) => s.as_bytes().len(),
                    _ => unreachable!(),
                };
                state.vals[state.base + a] = LBoxed::box_lvalue(LValue::Number(Number(n as _)));
            })));
            yield YieldOp::SetTypes(vec![(a, LType::Number)]);
            return arg;
        }
        arg = yield YieldOp::Guard(b, LType::Table);
        if ResumeArg::Matched == arg {
            // TODO: __len metamethod
            arg = yield YieldOp::Exec(ResidualExec::new("len_tab", Rc::new(move |owner, state| {
                let LValue::Table(b) = state.vals[state.base + b].unbox() else { unreachable!() };
                let n = b.ro(owner).array.len();
                state.vals[state.base + a] = LBoxed::box_lvalue(LValue::Number(Number(n as _)));
            })));
            yield YieldOp::SetTypes(vec![(a, LType::Number)]);
            return arg;
        } else {
            unimplemented!("__len metamethod")
        }

        arg
    }
}

pub fn emit_concat(a: usize, b: usize, c: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        for i in (b as usize)..=(c as usize) {
            // Weird, but we can do it
            arg = yield YieldOp::Guard(i, LType::String);
        }
        arg = yield YieldOp::Exec(ResidualExec::new("concat", Rc::new(move |owner, state| {
            let mut s: FVec<_> = vec![].into();
            for i in (b as usize)..=(c as usize) {
                match state.vals[state.base + i as usize].unbox() {
                    LValue::OwnedString(g) => s.extend_from_slice(g.as_slice()),
                    LValue::InternedString(is) => s.extend_from_slice(is.as_bytes()),
                    _ => unreachable!(),
                }
            }
            debug!("concat {:?}", String::from_utf8_lossy(s.as_slice()));
            state.vals[state.base + a as usize] = LBoxed::box_lvalue(LValue::OwnedString(crate::gc::Gc::new(s)));
        })));
        arg = yield YieldOp::SetTypes(vec![(a, LType::String)]);
        // It allocates. See Note [Block safepoints].
        yield YieldOp::CollectGarbage;
        arg
    }
}


pub fn emit_move(dest: usize, src: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Typeof(src);
        if let ResumeArg::Type(t) = arg.clone() {
            windowed!(Move, [], [], |owner, state, base| (from, out to) {
                *to = from;
            });
            yield YieldOp::ExecWindow(Rc::new(Move::new(&[src, dest])));
            // TODO: track references? see PyLBBV
            debug!("move {} = {} {:?}", dest, src, t);
            yield YieldOp::SetCTypes(vec![(dest, t)]);
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
        windowed!(GetUpval, [index: usize], [], |owner, state, base| (out dest) {
            let upval = match state.clos.ro(owner).upvalues[index].deref().ro(owner) {
                Upvalue::Open(o) => {
                    // The running closure's upvalues were captured by an enclosing
                    // function, so an open one is a slot of an enclosing frame, not
                    // one of this frame's (which the window may cache).
                    assert!(*o < state.base, "open upvalue in the running frame");
                    state.vals[*o as usize]
                },
                Upvalue::Closed(c) => *c.ro(owner),
            };
            debug!("upval {:?}", &upval);
            *dest = upval;
        });
        arg = yield YieldOp::ExecWindow(Rc::new(GetUpval::new(b, &[a])));
        // TODO: We can resolve upvalues to types, but would need to make sure to
        // keep them synced with the type of the stack slot or SETUPVAL/calls.
        arg = yield YieldOp::SetTypes(vec![(a, LType::Unknown)]);
        return arg;
    }
}

pub fn emit_self(a: usize, b: usize, c: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        let mut getmem = emit_gettable(a, b, c);
        drain!(getmem, arg);
        let mut moveself = emit_move(a + 1, b);
        drain!(moveself, arg);
        ResumeArg::Start
    }
}

pub fn emit_forprep(a: usize, sbx: i32, pc: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        debug!("forprep {a} {sbx} {pc}");
        // An integer loop's index, limit and step are integers: find out which
        // are. See Note [Integers].
        for slot in a..a + 3 {
            yield YieldOp::GuardCType(slot, CType::Integer);
        }
        let mut sub = emit_numeric(Opcode::SUB, a, a, a + 2);
        drain!(sub, arg);
        arg = yield YieldOp::GetBlock(((pc as isize) + sbx as isize) as usize);
        let ResumeArg::BlockId(target) = arg else { unreachable!() };
        yield YieldOp::Jump(target);
        return arg;
    }
}

// FORLOOP's test, reading its index, limit and step in the integer encoding as
// `II`, `LI` and `SI` say (see Note [Integers]), and comparing them as integers
// if all are.
//
// Lua sets the loop variable only when the loop continues, but it is local to
// the loop's body: after the loop exits nothing reads it before writing it,
// and a closure capturing it has it closed (`CLOSE`) at the end of each
// iteration, before this runs. So it is set on exit too, and the op needn't
// read its old value.
crate::window::windowed!(ForLoop, [], [II: bool, LI: bool, SI: bool], |owner, state, base| (idx, limit, step, out var) {
    let comp = if II && LI && SI {
        let (nidx, nlimit, nstep) = (idx.as_int(), limit.as_int(), step.as_int());
        if nstep < 0 { nlimit <= nidx } else { nidx <= nlimit }
    } else {
        let (nidx, nlimit, nstep) = (number::<II>(idx), number::<LI>(limit), number::<SI>(step));
        if nstep < 0.0 { nlimit <= nidx } else { nidx <= nlimit }
    };
    *var = idx;
    state.select = if comp { 0 } else { 1 };
});

/// `ForLoop`, reading integers as `ii`, `li` and `si` say.
fn for_loop(ii: bool, li: bool, si: bool, operands: &[usize]) -> Rc<dyn Window> {
    match (ii, li, si) {
        (false, false, false) => Rc::new(ForLoop::<false, false, false>::new(operands)),
        (false, false, true) => Rc::new(ForLoop::<false, false, true>::new(operands)),
        (false, true, false) => Rc::new(ForLoop::<false, true, false>::new(operands)),
        (false, true, true) => Rc::new(ForLoop::<false, true, true>::new(operands)),
        (true, false, false) => Rc::new(ForLoop::<true, false, false>::new(operands)),
        (true, false, true) => Rc::new(ForLoop::<true, false, true>::new(operands)),
        (true, true, false) => Rc::new(ForLoop::<true, true, false>::new(operands)),
        (true, true, true) => Rc::new(ForLoop::<true, true, true>::new(operands)),
    }
}

pub fn emit_forloop(a: usize, sbx: i32, pc: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        debug!("forloop {a} {sbx} {pc}");
        debug!("{} {}", a, sbx);
        let mut add = emit_numeric(Opcode::ADD, a, a, a + 2);
        drain!(add, arg);

        // Integers are decoded, not lowered. See Note [Integers].
        let integer = ResumeArg::Type(CType::Integer);
        let ii = (yield YieldOp::Typeof(a)) == integer;
        let li = (yield YieldOp::Typeof(a + 1)) == integer;
        let si = (yield YieldOp::Typeof(a + 2)) == integer;
        let idx_number = if ii { ResumeArg::Matched } else { yield YieldOp::Guard(a, LType::Number) };
        let limit_number = if li { ResumeArg::Matched } else { yield YieldOp::Guard(a + 1, LType::Number) };
        let step_number = if si { ResumeArg::Matched } else { yield YieldOp::Guard(a + 2, LType::Number) };

        match (idx_number, limit_number, step_number) {
            (ResumeArg::Matched, ResumeArg::Matched, ResumeArg::Matched) => {
                yield YieldOp::ExecWindow(for_loop(ii, li, si, &[a, a + 1, a + 2, a + 3]));
                let ResumeArg::Type(t) = (yield YieldOp::Typeof(a)) else { unreachable!() };
                yield YieldOp::SetCTypes(vec![(a + 3, t)]);
            },
            _ => {
                yield YieldOp::Exec(ResidualExec::new("forloop_other", Rc::new(move |owner, state| {
                    panic!("forloop induction variable metamethod");
                })));
                yield YieldOp::SetTypes(vec![(a + 3, LType::Unknown)]);
            },
        }
        // The targets are versioned for the context the op leaves, with the loop
        // variable's type set.
        // TODO: `comp` metamethods? which may invalidate the types that our resolved
        // blocks are compatible for? i think they're fine because they're on the stack whatever
        arg = yield YieldOp::GetBlock(pc);
        let ResumeArg::BlockId(fallthrough) = arg else { unreachable!() };
        arg = yield YieldOp::GetBlock((pc as isize + sbx as isize) as usize);
        let ResumeArg::BlockId(taken) = arg else { unreachable!() };
        // For debug tracing, statically document that we have two outgoing edges
        yield YieldOp::Select(vec![("forloop_start", taken), ("forloop_finish", fallthrough)]);
        arg
    }
}

pub fn emit_call(a: usize, b: usize, c: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Guard(a, LType::Closure);
        if arg != ResumeArg::Matched {
            arg = yield YieldOp::Exec(ResidualExec::new("call_meta", Rc::new(move |owner, state| {
                debug!("??? {arg:?}");
                panic!("call metamethod {} {:?} {:?}", a, &state.vals, &state.vals[state.base + a])
            })));
            return arg;
        }
        // TODO: track concrete function targets at the type level, and emit a YieldOp::Dispatch
        // guard here for specializing the call + return continuation for each one.
        arg = yield YieldOp::Call(CallTarget::Dynamic(a, b, c));
        arg = yield YieldOp::SetHazards(None, None);
        arg
    }
}

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
pub struct ThunkRef(pub Rc<RefCell<dyn FnMut(&mut Specializer, &mut Owner, &mut RunState, usize) -> ()>>);

impl std::fmt::Debug for ThunkRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "Thunk(...)") }
}

#[derive(Debug, Clone)]
pub enum Residual {
    Guard { idx: usize, expected: LType },
    Exec(ResidualExec),
    /// A copy&patch window op (see `crate::window`): a trait object, like
    /// `Exec`'s closure, so processing sites never enumerate ops. Its operands
    /// are whole `LBoxed` values held in the register window.
    ExecWindow(Rc<dyn Window>),
    /// A guard whose test is a window op: it sets `state.select` to 0 to pass,
    /// taking the success edge (the residual after the next), or 1 to fail,
    /// falling through to the failure edge, as `Guard` does. See Note [Dynamic
    /// guards].
    GuardDynamic(Rc<dyn Window>),
    Call { a: u16, b: u16, c: u16 },
    Select(Vec<(&'static str, BlockId)>),
    Jump(BlockId),
    Thunk(ThunkRef),
    Ret(Pc, u8, u16),
    HashGuard { tab: usize, href: HashRef, expected: LType },
    EpochCheck { tab: usize, href: HashRef },
    NativeGuard { idx: usize, ptr: *const () },
    NativeCall { nf: NativeFunc, a: u16, b: u16, c: u16 },
    LuaCall { lclos: Tc<LClosure<'static, 'static>>, a: u16, b: u16, c: u16 },
    LuaGuard { idx: usize, ptr: *const () },
    GC,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum CType {
    Type(LType),
    /// A number that is a whole number in the i32 range. See Note [Integers].
    Integer,
    Shape(SmallVec<[HashRef; 4]>),
    NativeFunction(NClosure),
    LuaFunction(Tc<LClosure<'static, 'static>>),
}

impl Mark for CType {
    fn mark(&self, owner: &Owner) {
        match self {
            CType::LuaFunction(c) => c.mark(owner),
            _ => { },
        }
    }
}

impl CType {
    /// Whether a block specialized to `self` is correct for a value of type
    /// `other`: `self` is `other`, or above it in the lattice. See Note
    /// [Version compatibility].
    fn accepts(&self, other: &CType) -> bool {
        match (self, other) {
            (a, b) if a == b => true,
            (CType::Type(LType::Unknown), _) => true,
            (CType::Type(LType::Number), CType::Integer) => true,
            (CType::Type(LType::Closure), CType::NativeFunction(_) | CType::LuaFunction(_)) => true,
            _ => false,
        }
    }

    /// The type's height in the lattice: how much it tells.
    fn depth(&self) -> usize {
        match self {
            CType::Type(LType::Unknown) => 0,
            CType::Type(_) => 1,
            _ => 2,
        }
    }

    /// The most specific type accepting both.
    fn join(&self, other: &CType) -> CType {
        if self.accepts(other) {
            self.clone()
        } else if other.accepts(self) {
            other.clone()
        } else if self.as_ltype() == other.as_ltype() {
            CType::Type(self.as_ltype())
        } else {
            CType::Type(LType::Unknown)
        }
    }

    /// Convert a CType to an LType, potentially losing static information.
    fn as_ltype(&self) -> LType {
        match self {
            CType::Type(ty) => ty.clone(),
            CType::Integer => LType::Number,
            CType::Shape(_) => LType::Table,
            CType::NativeFunction(_) => LType::Closure,
            CType::LuaFunction(_) => LType::Closure,
        }
    }
}

impl std::fmt::Display for CType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CType::Type(ltype) => ltype.fmt(f),
            CType::Integer => write!(f, "integer"),
            CType::Shape(shape) => write!(f, "shape({})", shape.iter().map(|hr| hr.0.to_string()).intersperse(",".to_string()).collect::<String>()),
            CType::NativeFunction(func) => write!(f, "native_fn({:?})", func),
            CType::LuaFunction(lclos) => write!(f, "fn({:?})", lclos.as_ptr()),
        }
    }
}

// Note [Integers]
// ~~~~~~~~~~~~~~~
// `CType::Integer` is a number that is a whole number in the i32 range, but
// not -0, held in the integer encoding (Note [Integer encoding] in `lboxed`): a
// stack slot is in the integer encoding exactly when its context types it
// `Integer`. Every other number is a double, and nothing outside LBBV code
// sees an integer: no closure captures a slot of a frame LBBV runs, as it has
// no CLOSURE.
//
// They are found by demand: an op that wants an integer (a table key,
// FORPREP's operands) yields `GuardCType(slot, Integer)`, which answers
// statically when the context knows (the slot is `Integer`, or not a number)
// and otherwise ends the block in a discovery thunk, like `Guard`'s. Forcing
// it tests the value it finds:
//
//   * an integer: a `GuardDynamic(CheckInteger<true>)`, continuing on the
//     success path with the slot `Integer`, through a block converting it
//     (`ToInteger`);
//   * another number: a `GuardDynamic(CheckInteger<false>)`, continuing on the
//     failure path with the slot a number;
//   * anything else: a `Guard` on its type, continuing on the failure path.
//
// Its fail thunk does the same for the next value that fails the guard.
//
// An integer is lowered back to a double (`ToNumber`, typing its slot a
// number) wherever code would read it as any number or value: at a
// `Guard(slot, Number)`, and a `Demote` by an op handing it to generic code (a
// store to a table or a global, a table op's generic path), for a call's
// arguments and a return's values, and before a jump into a version typing the
// slot less precisely (Note [Version compatibility]), in a block of its own on
// that edge. A jump forgetting the types of registers holding no local keeps an
// integer's (`forgotten`), as forgetting it would lower it every time. Its context must still be one the version accepts, so a generator
// lowers nothing once it has its jump targets. `Typeof` answers `Integer`, so
// MOVE copies an integer as one.
//
// Integer ops read and give integers. A whole i32 constant loads as one. ADD,
// SUB, MUL and MOD of two `Integer` operands give one, guarded by a
// `GuardDynamic` test that the exact result fits the encoding, which a failing
// one computes as doubles instead. Compares of two compare them as integers.
// With one operand an integer, these ask which part of the number sublattice
// the other is in (`DiscoverInteger`), like a `Typeof` restricted to numbers:
// an `Integer` or a number the context knows answers statically, taking the
// integer or the double op, and an unknown one is found out as by a
// `GuardCType`. A known number isn't tested, so arithmetic on doubles tests
// nothing. The double ops, compares and FORLOOP read an integer operand as a
// double, and FORPREP finds out whether its operands are integers, so an
// integer loop's index and variable stay ones.

/// Whether a jump forgets a type of a register holding no local in scope at
/// its target, which may still be an expression's temporary (`a and b or c`).
/// Not an `Integer`: forgetting one would lower it, a conversion on every jump
/// with it, where forgetting any other type costs nothing.
fn forgotten(ctype: &CType) -> bool {
    !matches!(ctype, CType::Type(LType::Unknown) | CType::Integer)
}

/// Whether `n` is a `CType::Integer`. See Note [Integers].
#[inline(always)]
pub fn is_integer(n: f64) -> bool {
    ((n as i32) as f64).to_bits() == n.to_bits()
}

// A `GuardDynamic` test: whether the value is a number that is (`INTEGER`) or
// isn't a `CType::Integer`, in either case a double. See Note [Integers].
crate::window::windowed!(CheckInteger, [], [INTEGER: bool], |owner, state, base| (value) {
    let pass = value.as_number().is_some_and(|n| is_integer(n) == INTEGER);
    state.select = (!pass) as usize;
});

// Convert a number between its encodings, in place: a double that is a
// `CType::Integer` to one, and back. See Note [Integers].
crate::window::windowed!(ToInteger, [], [], |owner, state, base| (inout value) {
    let Some(n) = value.as_number() else { core::hint::unreachable_unchecked() };
    *value = LBoxed::from_int(n.to_int_unchecked::<i32>());
});
crate::window::windowed!(ToNumber, [], [], |owner, state, base| (inout value) {
    *value = LBoxed::from_number(value.as_int() as f64);
});

// Note [Dynamic guards]
// ~~~~~~~~~~~~~~~~~~~~~~
// A `GuardDynamic` residual's test is a window op that reads its operands and
// sets `state.select`, 0 to pass and 1 to fail, and does nothing else. Its two
// edges continue the generator at different `SubPc`s, resumed with `Matched` or
// `Failed`, so their versions are told apart by the outcome and needn't differ
// in context: a test can speculate on what no ctype names, like whether a key is
// in a table's array part (`InArray`), for the instruction's next op alone.
// Nothing records it, so nothing invalidates it: the guard tests it each run.
//
// A generator yields `GuardDynamic(test)`, ending its block in a thunk. Forcing
// it runs the test on the values at hand, then lays out
//
//   passed: guard(test), thunk(fail side), jump(pass side)
//   failed: guard(test), jump(fail side), thunk(pass side)
//
// compiling the side the values took, and the other when first taken, as a jump
// in place of its thunk. With feature `no_dynamic_guards`, every such yield
// fails statically instead, to measure the blocks the guards cost (`just
// graph-guards`).
//
// `CheckInteger` guards with the same residual, but through `GuardCType`: what it
// finds is a ctype, which each side's context records. See Note [Integers].

/// The array part slot of a `CType::Integer` key. Keys below 1 wrap past any
/// array part.
#[inline(always)]
fn integer_slot(i: i32) -> usize {
    (i as i64 - 1) as usize
}

// `GuardDynamic` tests: whether a `CType::Integer` key, in a register or the
// constant `k`, is in a table's array part. See Note [Dynamic guards].
crate::window::windowed!(InArray, [], [], |owner, state, base| (table, key) {
    let LValue::Table(tab) = table.unbox() else { core::hint::unreachable_unchecked() };
    state.select = (integer_slot(key.as_int()) >= tab.ro(owner).array.len()) as usize;
});
crate::window::windowed!(InArrayK, [k: i32], [], |owner, state, base| (table) {
    let LValue::Table(tab) = table.unbox() else { core::hint::unreachable_unchecked() };
    state.select = (integer_slot(k) >= tab.ro(owner).array.len()) as usize;
});

/// The type of a constant.
fn constant_ctype<S: PartialEq + Eq>(k: &crate::chunk::Constant<S>) -> CType {
    match k {
        crate::chunk::Constant::Nil => CType::Type(LType::Nil),
        crate::chunk::Constant::Bool(_) => CType::Type(LType::Bool),
        crate::chunk::Constant::Number(n) if is_integer(n.0) => CType::Integer,
        crate::chunk::Constant::Number(_) => CType::Type(LType::Number),
        crate::chunk::Constant::String(_) => CType::Type(LType::String),
    }
}

// Note [Version compatibility]
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// A block specialized to a context is correct for any values its types
// describe, so a jump may enter a version whose context *accepts* its own:
// slot by slot the same type or one above it in the lattice
//
//   Unknown  >  each LType  >  Number > Integer, Closure > a known function
//
// (a shape accepts only itself), with the same hkeys, whose indexes the
// block's hash witnesses are at. An `Integer` a version types less precisely
// is lowered on the way in (Note [Integers]). A bytecode pc's first `MAX_VERSIONS`
// contexts each get a version. A jump past that enters the accepting version
// that tells the most (loses the least lattice height), and failing any, a
// version for the join of its context and every existing one's, which the
// contexts like those accept.
//
// Only jumps to a pc go through this. A block continuing a generator inside an
// instruction (a subblock) depends on that generator's own state as well as on
// its context, so it is only entered from the same context. Every cycle goes
// through a jump, so bounding the versions jumps enter bounds the subblocks;
// `HARD_MAX_VERSIONS` enforces it.

/// The versions of a pc before jumps to it reuse one. See Note [Version compatibility].
const MAX_VERSIONS: usize = 5;
/// The versions of a pc, or of a point in its instruction, past which
/// specialization panics. See Note [Version compatibility].
const HARD_MAX_VERSIONS: usize = 16;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Context {
    pub types: SmallVec<[CType; 8]>,
    pub hkeys: Vec<HashKey<'static, 'static>>,
}

impl Mark for Context {
    fn mark(&self, owner: &Owner) {
        for ctype in &self.types {
            ctype.mark(owner);
        }
    }
}

impl Context {
    pub fn new(mut types: Vec<LType>) -> Self {
        Self {
            types: types.drain(..).map(|t| CType::Type(t)).collect(),
            hkeys: vec![],
        }
    }

    fn tostring(&self, owner: &Owner) -> String {
        format!("context([{}], hkeys: {})",
            self.types.iter().map(|t| format!("{}", t)).intersperse(",".to_string()).collect::<String>(),
            self.hkeys.iter().map(|hk| hk.tostring(owner)).intersperse(",".to_string()).collect::<String>(),
        )
    }

    /// The type of slot `idx`: unknown past the end.
    fn slot(&self, idx: usize) -> CType {
        self.types.get(idx).cloned().unwrap_or(CType::Type(LType::Unknown))
    }

    /// Whether a block specialized to `self` is correct in `other`. See Note
    /// [Version compatibility].
    fn accepts(&self, other: &Context) -> bool {
        self.hkeys == other.hkeys
            && (0..self.types.len().max(other.types.len())).all(|idx| self.slot(idx).accepts(&other.slot(idx)))
    }

    /// The lattice height `self` loses from `other`, which it accepts.
    fn distance(&self, other: &Context) -> usize {
        (0..self.types.len().max(other.types.len())).map(|idx| other.slot(idx).depth() - self.slot(idx).depth()).sum()
    }

    /// Widen `self` to accept `other`'s types too, forgetting every shape if
    /// their hkeys differ.
    fn join(&mut self, owner: &mut Owner, other: &Context) {
        let widened: Vec<(usize, CType)> = (0..self.types.len())
            .filter_map(|idx| {
                let joined = self.types[idx].join(&other.slot(idx));
                (joined != self.types[idx]).then_some((idx, joined))
            })
            .collect();
        self.set_types(owner, widened);
        if self.hkeys != other.hkeys {
            let shapes: Vec<(usize, CType)> = (0..self.types.len())
                .filter(|&idx| matches!(self.types[idx], CType::Shape(_)))
                .map(|idx| (idx, CType::Type(LType::Table)))
                .collect();
            self.set_types(owner, shapes);
        }
    }

    fn set_types(&mut self, owner: &mut Owner, ty_effects: Vec<(usize, CType)>) {
        for (idx, ty) in ty_effects {
            if idx > self.types.len() {
                self.types.resize(idx + 1, CType::Type(LType::Unknown));
            }
            // We may have shape(1) [hkey(1)], and then transiton a type back to an
            // ltable. Discovering the type again would transition to shape(2)
            // [hkey(1), hkey(2)] for no reason. We make sure to also forget about any
            // hkeys that are from the index we're forgetting about, first trying to
            // transition them to be owned by another shape that may be using the same
            // hkey instead (consider `local x = t; use(x.a); local y = x; x = nil;`,
            // where our move operator maintains types).
            // This does give us some slight block proliferation, since hkeys are still
            // path-dependent and you could end up with different indexes for hkeys,
            // and thus shape hrefs, depending on what other local variables you have
            // gotten rid of in your stack. It's probably possible to instead
            // de-duplicate structurally equivalent types in Specializer::find, however
            // that has the issue of runtime hash_witness entries referring to the same
            // path-dependent index and having to emit shuffles if you take a
            // de-duplicated branch but with different indexes.
            if let CType::Shape(shape) = &self.types[idx] {
                for (kidx, key) in self.hkeys.iter_mut().enumerate() {
                    if key.idx != idx { continue; }
                    // Try to migrate
                    let mut migrated = false;
                    for (new_idx, other_type) in self.types.iter().enumerate() {
                        if new_idx == idx { continue; }
                        let CType::Shape(other_shape) = other_type else { continue };
                        let hr: u8 = kidx.try_into().expect("too many hkeys");
                        if other_shape.contains(&HashRef(hr)) {
                            warn!("migrating {} to stack slot {}", kidx, new_idx);
                            key.idx = new_idx;
                            migrated = true;
                            break;
                        }
                    }
                    if !migrated {
                        key.known_type = CType::Type(LType::Unknown);
                    }
                }
                // We can only remove hkeys at the end of the array for the same
                // reason of needing stable hash_witness indexes. For interior ones, we
                // can mark them as LType::Unknown and try to re-use the index instead
                // of pushing to the array when we need a new HashKey in order to try
                // and re-use the slot (and potentially end up with the same
                // pre-SetTypes context entirely). This is safe because we only ever
                // have LType::Unknown as the known_type for an hkey before forcing an
                // href_thunk, which happens immediately.
                while let Some(_) = self.hkeys.pop_if(|hkey| hkey.idx == idx) { }
            }
            self.types[idx] = ty;
            warn!("set types to {:?}", &self.types);
        }
    }

    /// Set optimization hazards for a stack slot, potentially scoped to only information which
    /// can alias with a specific hash key, and potentially keeping intact information about a
    /// stack slot.
    pub fn set_hazards(&mut self, keep: Option<usize>, href: Option<HashRef>) {
        let mut invalidate: Vec<usize> = (0..self.hkeys.len()).collect();
        if let Some(href) = href {
            // If we know we wrote to an href, then we can set hazards only on hkeys
            // that have the same key value: writing to `x.a` may invalidate `y.a`, but never
            // `y.b`.
            let hkey = &self.hkeys[href.0 as usize].key;
            invalidate = self.hkeys.iter().enumerate().filter(|(i, hk)| hk.key == *hkey).map(|(i, _)| i).collect();
        }
        if let Some(keep) = keep {
            invalidate = invalidate.drain(..).filter(|i| self.hkeys[*i].idx != keep).collect();
        }
        for invalid in invalidate {
            for know in &mut self.hkeys[invalid as usize].hazards {
                if *know {
                    debug!("hazard cleared {invalid}");
                }
                *know = false;
            }
        }
    }
}

pub struct Specializer<'src, 'intern> {
    pub blocks: Vec<Block>,
    pub clos: Tc<LClosure<'src, 'intern>>,
    #[cfg(feature = "jit")]
    pub jctx: JitContext,

    pub versions: std::collections::HashMap<
        LProto<'src, 'intern>,
        std::collections::HashMap<(SubPc, Rc<Context>), BlockId, rustc_hash::FxBuildHasher>, InternedHasher>,
}

impl<'src, 'intern> Mark for Specializer<'src, 'intern> {
    fn mark(&self, owner: &Owner) {
        self.clos.mark(owner);
        for (proto, versions) in &self.versions {
            for (key, blockid) in versions {
                let (subpc, context) = key.deref();
                (*context).mark(owner);
            }
        }
    }
}

impl<'src, 'intern> Specializer<'src, 'intern> {
    pub fn new(clos: Tc<LClosure<'src, 'intern>>) -> Self {
        Self {
            blocks: Vec::new(),
            versions: HashMap::default(),
            #[cfg(feature = "jit")]
            jctx: JitContext::new(),
            clos,
        }
    }

    /// Create a new block at a Lua bytecode PC
    pub fn block(&mut self, owner: &mut Owner, entry: Pc, ctx: Rc<Context>) -> BlockId {
        let mut pc = entry;

        let block_id = self.new_block(entry);
        self.blocks[block_id.0].context = Some(ctx.clone());
        let subpc: SubPc = SubPc::new(entry);
        self.versions.get_mut(&self.clos.ro(owner).prototype).unwrap().insert((subpc, ctx.clone()), block_id);
        self.compile(owner, entry, ctx, block_id);
        return block_id;
    }

    pub fn subblock(&mut self, owner: &mut Owner, pc: SubPc, ctx: Rc<Context>, mut coro: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>, arg: ResumeArg) -> BlockId {
        if let Some(exists) = self.versions.get(&self.clos.ro(owner).prototype).unwrap().get(&(pc, ctx.clone())) {
            return exists.clone();
        }
        let count: Vec<_> = self.versions.get(&self.clos.ro(owner).prototype).unwrap().iter().filter(|((epc, ty), block)| *epc == pc).collect();
        if count.len() >= HARD_MAX_VERSIONS {
            panic!("too many versions: {:#?}", count);
        }
        // Finish the remainder of the coroutine
        let new_block = self.new_block(pc.0);
        self.versions.get_mut(&self.clos.ro(owner).prototype).unwrap().insert((pc, ctx.clone()), new_block);
        if let Some((succ_next, succ_ty, succ_ret)) = self.compile_one(owner, pc, ctx, coro, arg, new_block) {
            // And continue compiling the block
            self.compile(owner, succ_next, succ_ty, new_block);
        }

        return new_block;
    }


    /// The block a jump to `pc` in `ctx` enters: a version for `ctx`, or one
    /// accepting it, compiled if need be. See Note [Version compatibility].
    pub fn version(&mut self, owner: &mut Owner, pc: Pc, ctx: Rc<Context>) -> BlockId {
        let subpc = SubPc::new(pc);
        let versions = self.versions.get(&self.clos.ro(owner).prototype).unwrap();
        if let Some(&exists) = versions.get(&(subpc, ctx.clone())) {
            return exists;
        }
        let existing: Vec<(Rc<Context>, BlockId)> = versions
            .iter()
            .filter(|((epc, _), _)| *epc == subpc)
            .map(|((_, ectx), block)| (ectx.clone(), *block))
            .collect();
        if existing.len() < MAX_VERSIONS {
            return self.block(owner, pc, ctx);
        }
        let accepting = |ctx: &Context| {
            existing
                .iter()
                .filter(|(ectx, _)| ectx.accepts(ctx))
                .min_by_key(|(ectx, block)| (ectx.distance(ctx), block.0))
                .map(|(_, block)| *block)
        };
        if let Some(block) = accepting(&ctx) {
            return block;
        }
        let mut joined = (*ctx).clone();
        for (ectx, _) in &existing {
            joined.join(owner, ectx);
        }
        if let Some(block) = accepting(&joined) {
            return block;
        }
        if existing.len() >= HARD_MAX_VERSIONS {
            panic!("too many versions at {pc}: {:#?}", existing.iter().map(|(ectx, _)| ectx).collect::<Vec<_>>());
        }
        self.block(owner, pc, Rc::new(joined))
    }

    /// Return a specialized block for a given PC and context, compiling a new one if necessary
    pub fn find(&mut self, owner: &mut Owner, pc: SubPc, ctx: &Rc<Context>) -> Option<BlockId>
    {
        self.versions.get(&self.clos.ro(owner).prototype).unwrap().get(&(pc, ctx.clone())).cloned()
    }

    pub fn compile(&mut self, owner: &mut Owner, mut pc: Pc, mut ctx: Rc<Context>, block_id: BlockId) -> Rc<Context> {
        loop {
            let inst = unsafe { self.clos.ro(owner).prototype.as_ref().unwrap().instructions.items[pc].clone() };
            debug!("compile {pc} {:?} {:?}", inst.0.Opcode(), ctx);
            if let Some((next, nctx, ret)) = match inst.0.Opcode() {
                op @ (Opcode::ADD | Opcode::SUB | Opcode::MUL | Opcode::DIV | Opcode::MOD | Opcode::POW) => {
                    let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                    debug!("{a} {b} {c}");
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_numeric(op, a as usize, b as usize, c as usize)), ResumeArg::Start, block_id)
                },
                op @ (Opcode::EQ | Opcode::LT | Opcode::LE) => {
                    let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                    debug!("{a} {b} {c}");
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_compare(op, a, b as usize, c as usize, pc + 1)), ResumeArg::Start, block_id)
                },
                Opcode::TEST => {
                    let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_test(a as usize, c, pc + 1)), ResumeArg::Start, block_id)
                },
                Opcode::JMP => {
                    let sbx = crate::vm::sBx::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_jmp(sbx, pc + 1)), ResumeArg::Start, block_id)
                    //self.blocks[block_id].push(Residual::Jump(((pc as isize) + sbx as isize) as usize)); return ctx;
                },
                Opcode::UNM => {
                    let (a, b) = crate::vm::AB::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_unm(a as usize, b as usize)), ResumeArg::Start, block_id)
                },
                Opcode::LEN => {
                    let (a, b) = crate::vm::AB::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_len(a as usize, b as usize)), ResumeArg::Start, block_id)
                },
                Opcode::CONCAT => {
                    let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_concat(a as usize, b as usize, c as usize)), ResumeArg::Start, block_id)
                },
                Opcode::LOADK => {
                    let (a, bx) = crate::vm::ABx::unpack(inst.0);
                    let c: LValue<'src, 'intern> = unsafe { (&(&(*self.clos.ro(owner).prototype).constants.items)[bx as usize]).into() };
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_loadk(bx, c.typeof_(), a as usize)), ResumeArg::Start, block_id)
                },
                Opcode::LOADNIL => {
                    let (a, b) = crate::vm::AB::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_loadnil(a as usize, b as usize)), ResumeArg::Start, block_id)
                },
                Opcode::LOADBOOL => {
                    let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_loadbool(a as usize, b != 0, c != 0, pc + 1)), ResumeArg::Start, block_id)
                },
                Opcode::MOVE => {
                    let (a, b) = crate::vm::AB::unpack(inst.0);
                    debug!("move {} {}", a, b);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_move(a as usize, b as usize)), ResumeArg::Start, block_id)
                },
                Opcode::FORPREP => {
                    let (a, sbx) = crate::vm::AsBx::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_forprep(a as usize, sbx, pc + 1)), ResumeArg::Start, block_id)
                },
                Opcode::FORLOOP => {
                    let (a, sbx) = crate::vm::AsBx::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_forloop(a as usize, sbx, pc + 1)), ResumeArg::Start, block_id)
                },
                Opcode::GETUPVAL => {
                    let (a, b) = crate::vm::AB::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_getupval(a as usize, b as usize)), ResumeArg::Start, block_id)
                },
                Opcode::SELF => {
                    let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_self(a as usize, b as usize, c as usize)), ResumeArg::Start, block_id)
                },
                Opcode::CALL => {
                    let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                    debug!("{} {} {}", a, b, c);
                    // TODO: this should try to compile a new block and jump to it, and only
                    // fallback to a trace exit if we need to run the fully generic code
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_call(a as usize, b as usize, c as usize)), ResumeArg::Start, block_id)
                },
                Opcode::GETGLOBAL => {
                    let (a, bx) = crate::vm::ABx::unpack(inst.0);
                    let kst = unsafe { &(&(*self.clos.ro(owner).prototype).constants.items)[bx as usize] };
                    debug!("getglobal {} {} {:?}", a, bx, &kst);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_getglobal(a as usize, kst)), ResumeArg::Start, block_id)
                },
                Opcode::SETGLOBAL => {
                    let (a, bx) = crate::vm::ABx::unpack(inst.0);
                    let kst = unsafe { &(&(*self.clos.ro(owner).prototype).constants.items)[bx as usize] };
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_setglobal(a as usize, kst)), ResumeArg::Start, block_id)
                },
                Opcode::GETTABLE => {
                    let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                    debug!("gettable {} {} {}", a, b, c);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_gettable(a as usize, b as usize, c as usize)), ResumeArg::Start, block_id)
                },
                Opcode::SETTABLE => {
                    let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                    debug!("settable {} {} {}", a, b, c);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_settable(a as usize, b as usize, c as usize)), ResumeArg::Start, block_id)
                },
                Opcode::NEWTABLE => {
                    let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_newtable(a as usize, b as usize, c as usize)), ResumeArg::Start, block_id)
                },
                Opcode::SETLIST => {
                    let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_setlist(a as usize, b as usize, c as usize)), ResumeArg::Start, block_id)
                },
                Opcode::RETURN => {
                    let (a, b) = crate::vm::AB::unpack(inst.0);
                    let end = if b == 0 { usize::MAX } else { a as usize + b as usize - 1 };
                    self.demote(block_id, &mut ctx, a as usize..end);
                    self.end_block(block_id);
                    self.blocks[block_id.0].instructions.push(Residual::Ret(pc, a, b)); None
                },
                x => {
                    #[cfg(debug_assertions)]
                    {
                        unreachable!("{:?}", x)
                    }
                    panic!("{:?}", x);
                    self.blocks[block_id.0].instructions.push(Residual::Ret(pc, 0, 0)); None
                },
            } {
                pc = next;
                ctx = nctx;
                debug!("-> {}", next);
            } else {
                return ctx;
            }
        }
    }

    /// Lower the integers in `slots` to doubles, for code reading them as any
    /// value. See Note [Integers].
    fn demote(&mut self, block_id: BlockId, ctx: &mut Rc<Context>, slots: std::ops::Range<usize>) {
        for idx in slots.start..slots.end.min(ctx.types.len()) {
            if ctx.types[idx] == CType::Integer {
                self.blocks[block_id.0].instructions.push(Residual::ExecWindow(Rc::new(ToNumber::new(&[idx]))));
                Rc::make_mut(ctx).types[idx] = CType::Type(LType::Number);
            }
        }
    }

    /// Where a jump in `ctx` to `target` goes: to a version of a pc, through a
    /// block lowering the integers it types less precisely first. See Note
    /// [Integers].
    fn edge(&mut self, owner: &mut Owner, ctx: &Context, target: BlockId) -> BlockId {
        let Some(entered) = self.blocks[target.0].context.clone() else { return target };
        let pc = self.blocks[target.0].pc;
        // Every integer the version doesn't keep: one that joined with another
        // type into a less precise one.
        let lower: Vec<usize> = (0..ctx.types.len())
            .filter(|&idx| ctx.types[idx] == CType::Integer && entered.slot(idx) != CType::Integer)
            .collect();
        let live = unsafe { self.clos.ro(owner).prototype.as_ref().unwrap() }.locals_in_scope(pc).unwrap_or(usize::MAX);
        let mut jumping = ctx.clone();
        jumping.set_types(owner, lower.iter().map(|&idx| (idx, CType::Type(LType::Number))).collect());
        let dead = (live..jumping.types.len()).filter(|&idx| forgotten(&jumping.types[idx])).map(|idx| (idx, CType::Type(LType::Unknown))).collect();
        jumping.set_types(owner, dead);
        assert!(entered.accepts(&jumping), "a jump in {} to a version for {}", jumping.tostring(owner), entered.tostring(owner));
        if lower.is_empty() {
            return target;
        }
        let lowering = self.new_block(pc);
        for idx in lower {
            self.blocks[lowering.0].instructions.push(Residual::ExecWindow(Rc::new(ToNumber::new(&[idx]))));
        }
        self.blocks[lowering.0].instructions.push(Residual::Jump(target));
        lowering
    }

    /// Before the residual ending a block: its GC safepoint, if it may have
    /// allocated since its last. See Note [Block safepoints].
    fn end_block(&mut self, block_id: BlockId) {
        let block = &mut self.blocks[block_id.0];
        if std::mem::take(&mut block.allocates) {
            block.instructions.push(Residual::GC);
        }
    }

    /// A new, empty block starting at `pc` (see `Block::pc`).
    pub fn new_block(&mut self, pc: Pc) -> BlockId {
        self.blocks.push(Block::new(pc));
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

    /// Replace the thunk at `off` in `block` with a jump to `target`, and its
    /// JIT code too, if any, once `target` has some. See Note [Thunk patching].
    pub fn jump_thunk(&mut self, block: BlockId, off: usize, target: BlockId) {
        self.blocks[block.0].instructions[off] = Residual::Jump(target);
        #[cfg(feature = "jit")]
        self.link_thunk(block, off, target);
    }

    /// Whether `block` has JIT code, so a thunk in it must be forced into a
    /// jump. See Note [Thunk patching].
    fn compiled(&self, block: BlockId) -> bool {
        #[cfg(feature = "jit")]
        return self.jctx.blocks.contains_key(&block);
        #[cfg(not(feature = "jit"))]
        return false;
    }

    /// The thunk a `GuardDynamic` yield ends its block in. See Note [Dynamic guards].
    fn make_dynamic_thunk(&self, block_id: BlockId, thunk_coro: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>, test: Rc<dyn Window>, pc: SubPc, thunk_ctx: Rc<Context>) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            test.interp(owner, state);
            let passed = state.select == 0;
            // In place, unless the thunk's JIT code can only be patched to a jump.
            // See Note [Thunk patching].
            let block = if vm.compiled(block_id) {
                let guard_block = vm.new_block(pc.0);
                vm.jump_thunk(block_id, thunk_pc, guard_block);
                vm.blocks[guard_block.0].instructions.push(Residual::GuardDynamic(test.clone()));
                guard_block
            } else {
                vm.blocks[block_id.0].instructions[thunk_pc] = Residual::GuardDynamic(test.clone());
                block_id
            };
            let (fail, pass) = if passed {
                let pass = vm.subblock(owner, pc.next_true(), thunk_ctx.clone(), thunk_coro.clone(), ResumeArg::Matched);
                let fail = vm.make_side_thunk(block, thunk_coro.clone(), pc.next_false(), thunk_ctx.clone(), ResumeArg::Failed);
                (Residual::Thunk(fail), Residual::Jump(pass))
            } else {
                let fail = vm.subblock(owner, pc.next_false(), thunk_ctx.clone(), thunk_coro.clone(), ResumeArg::Failed);
                let pass = vm.make_side_thunk(block, thunk_coro.clone(), pc.next_true(), thunk_ctx.clone(), ResumeArg::Matched);
                (Residual::Jump(fail), Residual::Thunk(pass))
            };
            vm.blocks[block.0].instructions.push(fail);
            vm.blocks[block.0].instructions.push(pass);
        })))
    }

    /// A `GuardDynamic`'s side not yet taken, compiled and jumped to in its
    /// place when first taken. See Note [Dynamic guards].
    fn make_side_thunk(&self, block_id: BlockId, thunk_coro: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>, pc: SubPc, thunk_ctx: Rc<Context>, arg: ResumeArg) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            let side = vm.subblock(owner, pc, thunk_ctx.clone(), thunk_coro.clone(), arg.clone());
            vm.jump_thunk(block_id, thunk_pc, side);
        })))
    }

    /// `make_discovery_thunk`, for `GuardCType(idx, Integer)`. See Note [Integers].
    fn make_integer_thunk(&self, mut block_id: BlockId, thunk_coro: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>, idx: usize, pc: SubPc, thunk_ctx: Rc<Context>, appends: bool) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            let value = state.vals[state.base + idx].unbox();
            let mut forced_ctx = thunk_ctx.clone();
            let forced_mut = Rc::make_mut(&mut forced_ctx);
            let (guard, next, arg, integer) = match value {
                LValue::Number(n) if is_integer(n.0) => {
                    forced_mut.types[idx] = CType::Integer;
                    (Residual::GuardDynamic(Rc::new(CheckInteger::<true>::new(&[idx]))), pc.next_true(), ResumeArg::Matched, true)
                },
                LValue::Number(_) => {
                    forced_mut.types[idx] = CType::Type(LType::Number);
                    (Residual::GuardDynamic(Rc::new(CheckInteger::<false>::new(&[idx]))), pc.next_false(), ResumeArg::Failed, false)
                },
                value => {
                    let runtime_type = value.typeof_();
                    forced_mut.types[idx] = CType::Type(runtime_type);
                    (Residual::Guard { idx, expected: runtime_type }, pc.next_false(), ResumeArg::Failed, false)
                },
            };
            // In place, unless the thunk's JIT code can only be patched to a
            // jump. See Note [Thunk patching].
            if !appends || vm.compiled(block_id) {
                let old_block = block_id;
                block_id = vm.new_block(pc.0);
                vm.jump_thunk(old_block, thunk_pc, block_id);
                vm.blocks[block_id.0].instructions.push(guard);
            } else {
                vm.blocks[block_id.0].instructions[thunk_pc] = guard;
            }
            let fail_thunk = vm.make_integer_thunk(block_id, thunk_coro.clone(), idx, pc, thunk_ctx.clone(), false);
            vm.blocks[block_id.0].instructions.push(Residual::Thunk(fail_thunk));
            let mut guard_block = vm.subblock(owner, next, forced_ctx, thunk_coro.clone(), arg);
            // An integer is converted on the edge into the subblock, which the
            // ways holding it as one already share.
            if integer {
                let converting = vm.new_block(pc.0);
                vm.blocks[converting.0].instructions.push(Residual::ExecWindow(Rc::new(ToInteger::new(&[idx]))));
                vm.blocks[converting.0].instructions.push(Residual::Jump(guard_block));
                guard_block = converting;
            }
            vm.blocks[block_id.0].instructions.push(Residual::Jump(guard_block));
        })))
    }

    fn make_discovery_thunk(&self, mut block_id: BlockId, thunk_coro: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>, idx: usize, expected: LType, pc: SubPc, mut thunk_ctx: Rc<Context>, appends: bool) -> ThunkRef {

        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
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
            let mut thunk_coro  = thunk_coro.clone();
            let runtime_type = state.vals[state.base + idx].unbox().typeof_();
            let mut forced_ctx = thunk_ctx.clone();;
            let mut forced_mut = Rc::make_mut(&mut forced_ctx);
            forced_mut.types[idx] = CType::Type(runtime_type);
            debug!("forcing thunk with {:?} == {:?}", runtime_type, expected);
            let arg = if runtime_type == expected { ResumeArg::Matched } else { ResumeArg::Failed };
            // TODO: search for if we already have a compatible block
            // In place, unless the thunk's JIT code can only be patched to a
            // jump. See Note [Thunk patching].
            if !appends || vm.compiled(block_id) {
                let old_block = block_id;
                block_id = vm.new_block(pc.0);
                vm.jump_thunk(old_block, thunk_pc, block_id);
                vm.blocks[block_id.0].instructions.push(Residual::Guard { idx, expected: runtime_type });
            } else {
                vm.blocks[block_id.0].instructions[thunk_pc] = Residual::Guard { idx, expected: runtime_type };
            }
            // Push the same thunk down for the next value that fails the guard
            let fail_thunk = vm.make_discovery_thunk(block_id, thunk_coro.clone(), idx, expected, pc, thunk_ctx.clone(), false);
            vm.blocks[block_id.0].instructions.push(Residual::Thunk(fail_thunk.clone()));
            // If we're in the success block and the guarded value is a native function, we can
            // also try to emit a guard to specialize the function value as well. This lets us
            // specialize code like `local print = print; print("xyz");`.
            let idx_ctype = state.vals[state.base + idx].unbox().ctypeof_();
            if let CType::NativeFunction(nf) = &idx_ctype {
                // We know this original value has the correct native function, and so can compile
                // a block for it immediately.
                forced_mut.types[idx] = idx_ctype.clone();
                let guard_block = vm.subblock(owner, pc.next_true(), forced_ctx, thunk_coro, arg);
                // However future executions may have change the native function out from under us.
                // Emit a guard for the pointer identity: if it passes we're fine, but if it fails
                // we have to do this all over again with the newly observed type (up to our block
                // limit).
                let call = nf.get_ptr();
                vm.blocks[block_id.0].instructions.push(Residual::NativeGuard { idx, ptr: call });
                // TODO: this fail thunk could be a bit more efficient, where it doesn't actually
                // need to re-emit the Guard against Closure - but also it's unlikely to matter
                // much.
                vm.blocks[block_id.0].instructions.push(Residual::Thunk(fail_thunk));
                vm.blocks[block_id.0].instructions.push(Residual::Jump(guard_block));
            } else if let CType::LuaFunction(lclos) = &idx_ctype {
                // Likewise we can do the same thing with statically known Lua functions
                forced_mut.types[idx] = idx_ctype.clone();
                let guard_block = vm.subblock(owner, pc.next_true(), forced_ctx, thunk_coro, arg);
                let proto = lclos.ro(owner).prototype.cast();
                vm.blocks[block_id.0].instructions.push(Residual::LuaGuard { idx, ptr: proto });
                vm.blocks[block_id.0].instructions.push(Residual::Thunk(fail_thunk));
                vm.blocks[block_id.0].instructions.push(Residual::Jump(guard_block));
            } else {
                let guard_block = vm.subblock(owner, pc.next_true(), forced_ctx, thunk_coro, arg);
                vm.blocks[block_id.0].instructions.push(Residual::Jump(guard_block));
            }

            debug!("after compiling thunk, blocks look like {:?}", vm.blocks);
        })))
    }

    fn make_href_thunk(&self, mut block_id: BlockId, thunk_coro: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>, idx: usize, href: HashRef, pc: SubPc, mut thunk_ctx: Rc<Context>, appends: bool) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            let thunk_coro = thunk_coro.clone();
            let mut orig_ctx = thunk_ctx.clone();
            let thunk_mut = Rc::make_mut(&mut thunk_ctx);
            let hkey = &mut thunk_mut.hkeys[href.0 as usize];
            debug!("forcing href thunk for {idx} {href:?} {hkey:?}");
            let LValue::Table(tab) = state.vals[state.base + idx].unbox() else { unreachable!() };
            let Some((index, key, val)) = tab.ro(owner).hash.get_full(&LCanon::new((&hkey.key).into(), state.intern)) else {
                // The table doesn't have this key, which means we should actually just bailout
                let fail_block = vm.new_block(pc.0);
                if let Some((succ_next, succ_ty, succ_ret)) = vm.compile_one(owner, pc.next_false(), orig_ctx.clone(), thunk_coro, ResumeArg::Failed, block_id) {
                    vm.compile(owner, succ_next, succ_ty, fail_block);
                }
                vm.jump_thunk(block_id, thunk_pc, fail_block);
                return;
            };
            debug!("href forced by {tab:?} -> {val:?}");
            // TODO: give the environment a shape as well
            let discovered_type = val.unbox().typeof_();
            hkey.known_type = CType::Type(discovered_type);
            // Initialize the hkey after discovery with a cleared hazard for the index
            if hkey.hazards.len() <= idx {
                hkey.hazards.resize_with(idx + 1, || false);
                hkey.hazards[idx] = true;
            }

            // If we're loading a hashkey from a table and it's a native function, also try to
            // specialize on its value. This lets us devirtualize code like `local t = { print =
            // print }; t.print("xyz");`.
            if let CType::NativeFunction(nf) = state.vals[state.base + idx].unbox().ctypeof_() {
                debug!("todo href native function specialization");
            }

            // TODO: track the maximum number of hkeys + grow here instead so we can initialize the RunState
            // array.

            // Now transition into the populated hkey
            if let CType::Shape(existing) = &mut thunk_mut.types[idx] {
                existing.push(href)
            } else {
                thunk_mut.types[idx] = CType::Shape(vec![href].into());
            }
            let init_key = hkey.key.clone();
            let href_init = Residual::Exec(ResidualExec::new("href_init", Rc::new(move |owner, state| {
                let mut index = index;
                let hidx = state.witness_base + href.0 as usize;
                if state.hash_witnesses.len() <= hidx {
                    state.hash_witnesses.resize_with(hidx + 1, || None);
                }
                debug!("populating hashkey witness {}", hidx);
                let witness = &mut state.hash_witnesses[hidx];
                let LValue::Table(tab) = state.vals[state.base + idx].unbox() else { unreachable!() };
                let lkey = LCanon::new((&init_key).into(), state.intern);
                // Inline cache for assuming the index stays the same
                match tab.ro(owner).hash.get_index(index) {
                    Some((key, _)) if *key != lkey => {
                        debug!("href_init key mismatch, {:?} {:?}", key, lkey);
                        if let Some(new_index) = tab.ro(owner).hash.get_index_of(&lkey) {
                            index = new_index;
                            state.select = 0;
                        } else {
                            state.select = 1;
                        }
                    },
                    Some((key, _)) => {
                        state.select = 0
                    },
                    None => {
                        debug!("href_init missing key");
                        state.select = 1
                    },
                }
                *witness = Some(HashWitness {
                    href,
                    key: init_key.clone(),
                    epoch: tab.ro(owner).epoch,
                    index,
                });
            })));
            // In place, unless the thunk's JIT code can only be patched to a
            // jump. See Note [Thunk patching].
            if !appends || vm.compiled(block_id) {
                let old_block = block_id;
                block_id = vm.new_block(pc.0);
                vm.jump_thunk(old_block, thunk_pc, block_id);
                vm.blocks[block_id.0].instructions.push(href_init);
            } else {
                vm.blocks[block_id.0].instructions[thunk_pc] = href_init;
            }
            let has_key = vm.new_block(pc.0);
            let missing_key = vm.new_block(pc.0);
            vm.blocks[block_id.0].instructions.push(Residual::Select(
                vec![("has_key", has_key), ("missing_key", missing_key)]));
            let missing_coro = thunk_coro.clone();
            vm.blocks[missing_key.0].instructions.push(Residual::Thunk(ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
                debug!("missing key thunk");
                // Same as the outer thunk missing the key
                let fail_block = vm.new_block(pc.0);
                if let Some((succ_next, succ_ty, succ_ret)) = vm.compile_one(owner, pc.next_false(), orig_ctx.clone(), missing_coro.clone(), ResumeArg::Failed, fail_block) {
                    vm.compile(owner, succ_next, succ_ty, fail_block);
                }
                vm.jump_thunk(missing_key, thunk_pc, fail_block);
            })))));

            let guard_block = vm.subblock(owner, pc.next_true(), thunk_ctx.clone(), thunk_coro.clone(), ResumeArg::HashRef(href, CType::Type(discovered_type)));
            // TODO: do we need this? im pretty sure the answer is no, because we've always just
            // initialized it to the correct value.
            //vm.make_epoch_check(owner, has_key, thunk_coro, idx, href, pc, thunk_ctx.clone(), guard_block);
            vm.blocks[has_key.0].instructions.push(Residual::Jump(guard_block));
        })))
    }

    fn make_epoch_check(&mut self, owner: &mut Owner, block_id: BlockId, thunk_coro: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>, tab: usize, href: HashRef, pc: SubPc, thunk_ctx: Rc<Context>, success_block: BlockId) {
        // In order to assert that an href is still valid, we need to check that the witnessed
        // epoch is still the same: if so, all of its keys still have the same type as the
        // cached hashkey, and no additional hashkeys were inserted (which may otherwise cause
        // keys to shadow metatable keys, or resize the hashtable and invalidate pointers).
        // The epoch check block is behind a thunk, because since we dynamically track table
        // epoches in our witness table they only ever would fail if a table transitions its type
        // inside a block, which is unlikely to happen very often.
        let thunk_coro = thunk_coro.clone();
        self.blocks[block_id.0].instructions.push(Residual::EpochCheck { tab, href });
        // Build the thunk for if we fail the epoch check
        let fail_thunk = ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            debug!("hit epoch fail thunk");
            // The epoch is different, but the actual key type might still be the same.
            // Do another check for the key type, where if it still holds we can update the
            // witness epoch and jump back to the success block.
            let check_block = vm.new_block(pc.0);
            vm.jump_thunk(block_id, thunk_pc, check_block);
            let expected = &thunk_ctx.hkeys[href.0 as usize].known_type;
            // Because we will need to JIT the guards, we split "simple" hashguards from other, more
            // specialized ones such as for function targets.
            if let CType::NativeFunction(nf) = expected {
                let call = nf.get_ptr();
                vm.blocks[check_block.0].instructions.push(Residual::NativeGuard { idx: tab, ptr: call });
            } else if let CType::LuaFunction(lclos) = expected {
                let proto = lclos.ro(owner).prototype.cast();
                vm.blocks[check_block.0].instructions.push(Residual::LuaGuard { idx: tab, ptr: proto });
            }else {
                vm.blocks[check_block.0].instructions.push(Residual::HashGuard { tab, href: href.clone(), expected: expected.as_ltype() });
            }
            let update_href_thunk = vm.make_href_thunk(check_block, thunk_coro.clone(), tab, href.clone(), pc, thunk_ctx.clone(), false);
            vm.blocks[check_block.0].instructions.push(Residual::Thunk(update_href_thunk));
            vm.blocks[check_block.0].instructions.push(Residual::Exec(ResidualExec::new("epoch_repair", Rc::new(move |owner, state| {
                // Re-init the witness and jump back to success block
                let LValue::Table(t) = state.vals[state.base + tab].unbox() else { unreachable!() };
                let epoch = t.ro(owner).epoch;
                let Some(witness) = &mut state.hash_witnesses[state.witness_base + href.0 as usize] else { unreachable!() };
                debug!("repairing {:?} epoch", href);
                witness.epoch = epoch;
            }))));
            vm.blocks[check_block.0].instructions.push(Residual::Jump(success_block));
        })));
        self.blocks[block_id.0].instructions.push(Residual::Thunk(fail_thunk));
    }

    pub fn compile_one<C>(&mut self, owner: &mut Owner, mut pc: SubPc, mut ctx: Rc<Context>, mut coro: Box<C>, mut arg: ResumeArg, block_id: BlockId) -> Option<(Pc, Rc<Context>, ResumeArg)>
    where C: Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static
    {
        loop {
            let mut state = Pin::new(&mut coro).resume(arg);
            arg = ResumeArg::Start;
            'machine: loop { match state {
                CoroutineState::Yielded(YieldOp::TypeofK(k)) => {
                    let proto = self.clos.ro(owner).prototype;
                    arg = ResumeArg::Type(constant_ctype(unsafe { &(&(*proto).constants.items)[k] }));
                },
                CoroutineState::Yielded(YieldOp::IntegerK(k)) => {
                    let proto = self.clos.ro(owner).prototype;
                    let crate::chunk::Constant::Number(n) = (unsafe { &(&(*proto).constants.items)[k] }) else { unreachable!() };
                    assert!(is_integer(n.0), "{} isn't an integer", n.0);
                    arg = ResumeArg::Integer(n.0 as i32);
                },
                CoroutineState::Yielded(YieldOp::Demote(slots)) => {
                    self.demote(block_id, &mut ctx, slots);
                },
                op @ CoroutineState::Yielded(YieldOp::Typeof(idx) | YieldOp::TypeofRk(idx)) => {
                    if let CoroutineState::Yielded(YieldOp::TypeofRk(key)) = op {
                        let proto = self.clos.ro(owner).prototype;
                        if (key & 0x100)!=0 {
                            let k_const = key & (0xff);
                            arg = ResumeArg::Type(constant_ctype(unsafe { &(&(*proto).constants.items)[k_const as usize] }));
                            break 'machine;
                        }
                    }

                    let ctype = &ctx.types[idx];
                    arg = ResumeArg::Type(ctype.clone());
                },
                CoroutineState::Yielded(YieldOp::UpdateHashRef(href, ref ty)) => {
                    // We can't set a HashKey's type to Unknown, because then we'd think
                    // the slot is free to be reused (and it doesn't really make sense).
                    // Instead, we ignore the update and keep using the old type: there's
                    // a chance the unknown static type is in fact still our old type and
                    // we just didn't know, and if there is a runtime mismatch we will hit
                    // a type guard anyway.
                    let hkey = &mut Rc::make_mut(&mut ctx).hkeys[href.0 as usize];
                    if *ty != CType::Type(LType::Unknown) {
                        hkey.known_type = ty.clone();
                    }
                    // If we updated an href, then we also need to set optimization hazards for any
                    // potentially aliased ones. We also need to invalidate this stack slot as
                    // well.
                    state = CoroutineState::Yielded(YieldOp::SetHazards(None, Some(href)));
                    arg = ResumeArg::Failed;
                    continue 'machine;
                },
                op @ CoroutineState::Yielded(YieldOp::HashKey(idx, key) | YieldOp::TryHashKey(idx, key)) => {
                    let proto = self.clos.ro(owner).prototype;
                    if (key & 0x100)!=0 {
                        let k_const = key & (0xff);
                        let k_val = unsafe { &(&(*proto).constants.items)[k_const as usize] };
                        let ty = match unsafe { &(&(*proto).constants.items)[k_const as usize] } {
                            crate::chunk::Constant::Nil => LType::Nil,
                            crate::chunk::Constant::Bool(_) => LType::Bool,
                            crate::chunk::Constant::Number(_) => LType::Number,
                            crate::chunk::Constant::String(_) => LType::String,
                        };
                        if ty != LType::String {
                            // Only cache string keys
                            pc = pc.next_false();
                            arg = ResumeArg::Failed;
                            break 'machine;
                        }
                        match &ctx.types[idx] {
                            CType::Type(LType::Table) => {
                            },
                            CType::Shape(existing) => {
                                debug!("hashkey on existing shape {existing:?}");
                                for cached in existing {
                                    let cached_hkey = &ctx.hkeys[cached.0 as usize];
                                    if &cached_hkey.key == k_val {
                                        debug!("using cached href {:?}", cached);
                                        // We have a cached href, but still need to make sure that
                                        // it holds if there are any optimization hazards.
                                        // Compile a new block assuming the type holds, so that the
                                        // check can jump to it for spurious epoch increments (or
                                        // for blocks specialized for a different type that
                                        // transition back to our type).
                                        arg = ResumeArg::HashRef(cached.clone(), cached_hkey.known_type.clone());
                                        if let Some(true) = cached_hkey.hazards.get(idx) {
                                            // We can use the href without needing another epoch
                                            // check, because we know nothing could have
                                            // invalidated it.
                                            pc = pc.next_true();
                                            debug!("using cached hkey without hazards");
                                            break 'machine;
                                        }
                                        let mut holds_ctx = ctx.clone();
                                        // If we check the epoch and it still holds, we'll have
                                        // cleared any optimzation hazards until its potentially
                                        // invallidated.
                                        Rc::make_mut(&mut holds_ctx).hkeys[cached.0 as usize].hazards[idx] = true;
                                        let holds_block = self.subblock(owner, pc.next_true(), holds_ctx.clone(), coro.clone(), arg);
                                        self.make_epoch_check(owner, block_id, coro.clone(), idx, cached.clone(), pc, ctx.clone(), holds_block);

                                        self.end_block(block_id);
                                        self.blocks[block_id.0].instructions.push(Residual::Jump(holds_block));
                                        return None;
                                    }
                                }
                            },
                            _ => panic!("HashKey should only be used on a table"),
                        }
                        if matches!(op, CoroutineState::Yielded(YieldOp::TryHashKey(idx, key))) {
                            pc = pc.next_false();
                            arg = ResumeArg::Failed;
                            break 'machine;
                        }
                        let ty = match unsafe { &(&(*proto).constants.items)[k_const as usize] } {
                            crate::chunk::Constant::Nil => LType::Nil,
                            crate::chunk::Constant::Bool(_) => LType::Bool,
                            crate::chunk::Constant::Number(_) => LType::Number,
                            crate::chunk::Constant::String(_) => LType::String,
                        };
                        // We need these HashKeys to not have a lifetime, so that they can be
                        // captured by the generator: we only ever store the generator in the
                        // LClosure they came from, which is 'src 'lifetime, and so this is safe.
                        let k_val: &LConstant<'static, 'static> = unsafe { core::mem::transmute(k_val) };
                        // Try to find an orphaned HashKey slot to re-use
                        let href;
                        if let Some((i, hkey)) = Rc::make_mut(&mut ctx).hkeys.iter_mut().enumerate().find(|(i, hk)| hk.known_type == CType::Type(LType::Unknown)) {
                            href = HashRef(i as u8);
                            *hkey = HashKey { idx, key: k_val.clone(), known_type: CType::Type(LType::Unknown), hazards: Default::default() };
                        } else {
                            warn!("allocating new hkey for {} {:?}", idx, &k_val);
                            let hr: u8 = ctx.hkeys.len().try_into().expect("too many hrefs");
                            href = HashRef(hr);
                            let hkey = HashKey { idx, key: k_val.clone(), known_type: CType::Type(LType::Unknown), hazards: Default::default() };
                            #[cfg(debug_assertions)]
                            assert_eq!(ctx.hkeys.iter().filter(|exist| **exist == hkey).next(), None);
                            Rc::make_mut(&mut ctx).hkeys.push(hkey.clone());
                        }
                        let thunk_coro = coro.clone();
                        let thunk_ctx = ctx.clone();
                        let witness = Residual::Thunk(self.make_href_thunk(block_id, thunk_coro, idx, href.clone(), pc, thunk_ctx, true));
                        self.end_block(block_id);
                        self.blocks[block_id.0].instructions.push(witness);
                        return None;
                    } else {
                        pc = pc.next_false();
                        arg = ResumeArg::Failed;
                    }
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
                op @ CoroutineState::Yielded(YieldOp::GuardCType(_, _) | YieldOp::DiscoverInteger(_)) => {
                    let (rk, discover) = match op {
                        CoroutineState::Yielded(YieldOp::GuardCType(rk, expected)) => {
                            assert_eq!(expected, CType::Integer, "GuardCType tests only for Integer");
                            (rk, false)
                        },
                        CoroutineState::Yielded(YieldOp::DiscoverInteger(rk)) => (rk, true),
                        _ => unreachable!(),
                    };
                    let pass = if (rk & 0x100) != 0 {
                        let k = rk & 0xff;
                        let proto = self.clos.ro(owner).prototype;
                        let pass = constant_ctype(unsafe { &(&(*proto).constants.items)[k] }) == CType::Integer;
                        Some(if pass { ResumeArg::MatchedConst(k) } else { ResumeArg::Failed })
                    } else {
                        match &ctx.types[rk] {
                            CType::Integer => Some(ResumeArg::Matched),
                            CType::Type(LType::Number) if discover => Some(ResumeArg::Failed),
                            ctype if !matches!(ctype.as_ltype(), LType::Number | LType::Unknown) => Some(ResumeArg::Failed),
                            // A number, or unknown: tested at runtime. See Note [Integers].
                            _ => None,
                        }
                    };
                    match pass {
                        Some(ResumeArg::Failed) => {
                            pc = pc.next_false();
                            arg = ResumeArg::Failed;
                        },
                        Some(pass) => {
                            pc = pc.next_true();
                            arg = pass;
                        },
                        None => {
                            let thunk = Residual::Thunk(self.make_integer_thunk(block_id, coro.clone(), rk, pc, ctx.clone(), true));
                            self.end_block(block_id);
                            self.blocks[block_id.0].instructions.push(thunk);
                            return None;
                        },
                    }
                },
                CoroutineState::Yielded(YieldOp::GuardDynamic(test)) => {
                    assert!(test.accesses().iter().all(|access| *access == Access::Read), "{}: a guard's test has no outputs", test.name());
                    if cfg!(feature = "no_dynamic_guards") {
                        pc = pc.next_false();
                        arg = ResumeArg::Failed;
                    } else {
                        let thunk = Residual::Thunk(self.make_dynamic_thunk(block_id, coro.clone(), test, pc, ctx.clone()));
                        self.end_block(block_id);
                        self.blocks[block_id.0].instructions.push(thunk);
                        return None;
                    }
                },
                CoroutineState::Yielded(guard @ YieldOp::Guard(idx, expected)) => {
                    debug!("guard {:?} == {:?}", ctx.types[idx], expected);
                    let ctype = &ctx.types[idx];
                    // Erase any hkeys and say its just a table before checking
                    let ltype = ctype.as_ltype();

                    if ltype == expected {
                        // Statically true: pump the success path, with an
                        // integer read as a number lowered to a double. See
                        // Note [Integers].
                        if ctx.types[idx] == CType::Integer {
                            self.demote(block_id, &mut ctx, idx..idx + 1);
                        }
                        pc = pc.next_true();
                        arg = ResumeArg::Matched;
                    }
                    else if ltype != LType::Unknown {
                        // Statically false: pump the fail path
                        pc = pc.next_false();
                        arg = ResumeArg::Failed;
                    } else {
                        // Dynamic branch: create a thunk that will discovery the type of the
                        // guarded value when forced, and fork the coroutine for the observed case.
                        let thunk_coro = coro.clone();
                        let thunk_ctx = ctx.clone();
                        debug!("emitting discovery thunk");
                        let thunk = Residual::Thunk(self.make_discovery_thunk(block_id, thunk_coro, idx, expected, pc, thunk_ctx, true));
                        self.end_block(block_id);
                        self.blocks[block_id.0].instructions.push(thunk);
                        return None;
                    }
                }
                CoroutineState::Yielded(YieldOp::Exec(func)) => {
                    self.blocks[block_id.0].instructions.push(Residual::Exec(func));
                },
                CoroutineState::Yielded(YieldOp::ExecWindow(w)) => {
                    self.blocks[block_id.0].instructions.push(Residual::ExecWindow(w));
                },
                CoroutineState::Yielded(YieldOp::CollectGarbage) => {
                    self.blocks[block_id.0].allocates = true;
                },
                CoroutineState::Yielded(YieldOp::Select(targets)) => {
                    let targets = targets.into_iter().map(|(name, target)| (name, self.edge(owner, &ctx, target))).collect();
                    self.end_block(block_id);
                    self.blocks[block_id.0].instructions.push(Residual::Select(targets));
                    return None;
                },
                CoroutineState::Yielded(YieldOp::Call(target)) => {
                    let id;
                    match target {
                        CallTarget::Concrete(target) => {
                            // TODO: suspend coro so that it can be resumed after the target returns to
                            // compile the continuation
                            panic!();
                            if let Some(exists) = self.find(owner, SubPc::new(target), &ctx) {
                                id = exists;
                            } else {
                                debug!("compiling fresh callsite {} {:?}", target, ctx);
                                id = self.block(owner, target, ctx);
                            }
                        },
                        CallTarget::Dynamic(a, b, c) => {
                            // The callee reads its arguments as any value. See
                            // Note [Integers].
                            self.demote(block_id, &mut ctx, a + 1..if b == 0 { usize::MAX } else { a + b });
                            // A native run as a window op, with its arguments of the type it
                            // assumes, gives its result's type. See Note [Native windows].
                            let mut result = None;
                            if let CType::NativeFunction(nf) = &ctx.types[a] {
                                let op = nf
                                    .window(a, b as u16, c as u16)
                                    .filter(|op| (a + 1..a + b).all(|slot| ctx.types[slot].as_ltype() == op.args));
                                if let Some(op) = op {
                                    self.blocks[block_id.0].instructions.push(Residual::ExecWindow(op.window));
                                    result = Some(op.result);
                                } else {
                                    self.blocks[block_id.0].instructions.push(Residual::NativeCall {
                                        nf: nf.native(), a: a as u16, b: b as u16, c: c as u16
                                    });
                                    // A native may allocate (a table, a string).
                                    self.blocks[block_id.0].allocates = true;
                                }
                            } else if let CType::LuaFunction(lclos) = &ctx.types[a] {
                                // TODO: we should probably track the number of incoming edges, and
                                // subtract that count from the initial hotness of the entry block.
                                // Otherwise we will repeatedly bailout in the JIT as we trigger
                                // hotness=0 top-down instead of bottom-up.
                                self.blocks[block_id.0].instructions.push(Residual::LuaCall {
                                    lclos: lclos.clone(), a: a as u16, b: b as u16, c: c as u16
                                });
                            } else {
                                self.blocks[block_id.0].instructions.push(Residual::Call {
                                    a: a as u16, b: b as u16, c: c as u16
                                });
                                // It may call a native, which may allocate.
                                self.blocks[block_id.0].allocates = true;
                            }
                            // The results, and the callee's frame above them, overwrote
                            // every register from `a` on: their types are unknown.
                            // TODO: compile a type specialized thunk instead? is that better?
                            let clobbered: Vec<(usize, CType)> = (a..ctx.types.len())
                                .map(|idx| (idx, CType::Type(LType::Unknown)))
                                .collect();
                            Rc::make_mut(&mut ctx).set_types(owner, clobbered);
                            if let Some(result) = result {
                                Rc::make_mut(&mut ctx).types[a] = CType::Type(result);
                            }
                            return Some((pc.0 + 1, ctx, ResumeArg::Start));
                        },
                    }
                },
                CoroutineState::Yielded(YieldOp::SetTypes(mut ty_effects)) => {
                    Rc::make_mut(&mut ctx).set_types(owner, ty_effects.drain(..).map(|(idx, ty)| (idx, CType::Type(ty))).collect())
                },
                CoroutineState::Yielded(YieldOp::SetHazards(idx, href)) => {
                    Rc::make_mut(&mut ctx).set_hazards(idx, href)
                },
                CoroutineState::Yielded(YieldOp::SetCTypes(ty_effects)) => {
                    Rc::make_mut(&mut ctx).set_types(owner, ty_effects)
                },
                CoroutineState::Yielded(YieldOp::GetBlock(dest_pc)) => {
                    // The jump forgets the types of every register not holding a local in
                    // scope at its target (`forgotten`), which lets paths that differ
                    // only in them share the target's version.
                    let mut ctx = ctx.clone();
                    let in_scope = unsafe { self.clos.ro(owner).prototype.as_ref().unwrap() }.locals_in_scope(dest_pc);
                    if let Some(in_scope) = in_scope {
                        let dead: Vec<(usize, CType)> = (in_scope..ctx.types.len())
                            .filter(|&idx| forgotten(&ctx.types[idx]))
                            .map(|idx| (idx, CType::Type(LType::Unknown)))
                            .collect();
                        if !dead.is_empty() {
                            Rc::make_mut(&mut ctx).set_types(owner, dead);
                        }
                    }
                    // TODO: compiling the target here recurses, and potentially blows the
                    // stack; this should probably push a thunk which compiles the block
                    // instead of a jump
                    arg = ResumeArg::BlockId(self.version(owner, dest_pc, ctx));
                },
                CoroutineState::Yielded(YieldOp::Jump(dest_block)) => {
                    let dest_block = self.edge(owner, &ctx, dest_block);
                    self.end_block(block_id);
                    self.blocks[block_id.0].instructions.push(Residual::Jump(dest_block));
                    // If it was a jump, stop pumping the coroutine
                    return None;
                },
                CoroutineState::Complete(r) => {
                    return Some((pc.0 + 1, ctx, r));
                }
            } break 'machine; }
        }
    }

    pub fn run(&mut self, gc: GcCtx<'_>, owner: &mut Owner, mut id: BlockId, mut state: RunState<'src, 'intern>) -> (RunState<'src, 'intern>, Option<FVec<LBoxed<'src, 'intern>>>) {
        let mut off: usize = 0;
        debug!("run");
        // Republish on entry: `state` was moved into this frame (the caller's pointer is now
        // stale) and a JIT block can call a native before the first safepoint. See Note
        // [GC roots].
        gc.publish(&state, &*self);
        loop {
            #[cfg(feature = "gc_stress")]
            {
                // SAFETY: We have no unrooted variables or parameters.
                unsafe { gc.step(&state, &*self, owner); }
            }
            let block = &mut self.blocks[id.0];
            #[cfg(feature = "graph")]
            if off == 0 {
                block.entered += 1;
            }
            #[cfg(feature = "jit")]
            if off == 0 && state.gas > 0 {
                let hot = block.jit_info.hotness.get();
                if hot > 0 {
                    block.jit_info.hotness.set(hot - 1);
                } else {
                    if block.jit_info.entry.is_none() {
                        debug!("jit compile {id:?}");
                        self.jit_compile(id, owner);
                    }

                    let mut jit_entry = self.blocks[id.0].jit_info.entry.unwrap();
                    let base_ptr = unsafe { state.vals.stack_ptr.as_non_null_ptr().add(state.base).as_ptr() };
                    warn!("running jit for {id:?} with base_ptr {base_ptr:p}");
                    state.trap = false;
                    let ret = jit_entry(&mut state, base_ptr);
                    let next_off = (ret >> 32) as i32 as isize;
                    let next_id = (ret & 0xFFFFFFFF) as usize;
                    self.clos = state.clos.clone();

                    if next_off >= 0 {
                        debug!("jit exit to {next_id} {next_off}");
                        id = BlockId(next_id as usize);
                        off = next_off as usize;
                        continue;
                    } else if next_off == -1 {
                        debug!("jit bail 1 from {next_id}");
                        state.trap = false;
                        id = BlockId(next_id as usize);
                        off = state.current_off as usize;
                        // Fallthrough to continue post-trap in the interpreter
                    } else if next_off == -2 {
                        debug!("jit bail 2 from {next_id}");
                        id = BlockId(next_id as usize);
                        off = state.current_off as usize;
                        // Fallthrough to handle RET
                    } else if next_off == -3 {
                        debug!("jit bail 3 from {next_id}");
                        off = state.current_off as usize;
                        let Residual::Select(ref paths) = self.blocks[id.0].instructions[off] else { panic!() };
                        id = paths[state.select].1;
                        off = 0;
                        continue;
                    } else if next_off == -4 {
                        debug!("jit bail 4 from {next_id}");
                        state.trap = false;
                        id = BlockId(next_id as usize);
                        off = state.current_off as usize;
                        // Fallthrough to immediately handle the instruction: if we have a
                        // thunk at offset=0, we don't want to jump back to the JIT again.
                    } else if next_off == -5 {
                        // Returning to interpreter
                        debug!("jit bailout to interpreter");
                        return (state, None);
                    }
                }
            }
            if state.gas > 0 && state.gas < 100 {
                let res = self.blocks[id.0].instructions[off].clone();
                println!("low gas {} at {id:?} {off} {res:?}", state.gas);
            }
            if state.gas == 0 {
                let res = self.blocks[id.0].instructions[off].clone();
                println!("out of gas at {id:?} {off} {res:?}");
                println!("out of gas run state: base={:?}", state.base);
                println!("out of gas return stack: {:?}", state.callstack);
                state.gas -= 1;
            }
            let res = self.blocks[id.0].instructions[off].clone();
            state.counters.versioned_count.increment();
            debug!("RUN {:?}", &res);
            match res {
                Residual::Guard { idx, expected } => {
                    if state.vals[state.base + idx].unbox().typeof_() == expected {
                        // Fallthrough
                        off += 2;
                    } else {
                        off += 1;
                    }
                },
                Residual::NativeGuard { idx, ptr } => {
                    if let LValue::NClosure(nf) = state.vals[state.base + idx].unbox() {

                        let call = nf.get_ptr();
                        if call == ptr {
                            // Fallthrough
                            off += 2;
                        } else {
                            off += 1;
                        }
                    } else {
                        off += 1;
                    }
                },
                Residual::LuaGuard { idx, ptr } => {
                    if let LValue::LClosure(clos) = state.vals[state.base + idx].unbox() {
                        let call = clos.ro(owner).prototype.cast();
                        if call == ptr {
                            // Fallthrough
                            off += 2;
                        } else {
                            off += 1;
                        }
                    } else {
                        off += 1;
                    }
                },
                Residual::EpochCheck { tab, href } => {
                    let hwit = &state.hash_witnesses[state.witness_base + href.0 as usize].as_ref().unwrap();
                    let LValue::Table(tab) = state.vals[state.base + tab].unbox() else { unreachable!() };
                    warn!("epochcheck sees {} == {}", hwit.epoch, tab.ro(owner).epoch);
                    if hwit.epoch == tab.ro(owner).epoch {
                        // Fallthrough
                        off += 2;
                    } else {
                        off += 1;
                    }
                },
                Residual::HashGuard { tab, href, expected } => {
                    let hwit = &state.hash_witnesses[state.witness_base + href.0 as usize].as_ref().unwrap();
                    let LValue::Table(tab) = state.vals[state.base + tab].unbox() else { unreachable!() };
                    let Some((key, val)) = tab.ro(owner).hash.get_index(hwit.index) else { unreachable!() };
                    let cached_key = LCanon::new((&hwit.key).into(), state.intern);
                    #[cfg(debug_assertions)]
                    assert!(*key == cached_key);
                    if val.unbox().typeof_() == expected {
                        // Fallthrough
                        off += 2;
                    } else {
                        off += 1;
                    }
                },
                Residual::Select(targets) => {
                    id = targets[state.select].1;
                    off = 0;
                },
                Residual::Exec(f) => {
                    off += 1;
                    (f.body)(owner, &mut state);
                },
                Residual::ExecWindow(w) => {
                    off += 1;
                    w.interp(owner, &mut state);
                },
                Residual::GuardDynamic(w) => {
                    w.interp(owner, &mut state);
                    off += if state.select == 0 { 2 } else { 1 };
                },
                Residual::LuaCall { lclos, a, b, c } => {
                    off += 1;
                    // Safety: transmute the 'static lifetime back down. This is always shorter.
                    let lclos: Tc<LClosure<'src, 'intern>> = unsafe { core::mem::transmute(lclos) };
                    let next_stack = state.call_lua(owner, ReturnLocation::Generator(id, off).pack(), a, b, c);
                    // Either use existing block, compile a new one, or use most
                    // generic.
                    let types = vec![LType::Unknown; next_stack];
                    let ctx = Rc::new(Context::new(types));
                    self.versions.entry(lclos.ro(owner).prototype).or_insert_with(|| HashMap::default());
                    self.set_current(lclos.clone());
                    let block = self.version(owner, 0, ctx);
                    debug!("{:?} {block:?}", self.blocks);
                    self.set_current(lclos.clone());
                    id = block;
                    off = 0;
                    continue;
                },
                Residual::NativeCall { nf, a, b, c } => {
                    off += 1;
                    gc.publish(&state, &*self);
                    state.call_native(nf, a, b, c, owner);
                },
                Residual::Call { a, b, c } => {
                    off += 1;
                    let to_call = state.vals[state.base + a as usize].unbox();
                    debug!("{:?}", to_call);
                    // push where to return to once we RETURN
                    if let LValue::LClosure(ref lclos) = to_call {
                        let next_stack = state.call_lua(owner, ReturnLocation::Generator(id, off).pack(),
                            a as u16, b as u16, c as u16
                        );
                        // Either use existing block, compile a new one, or use most
                        // generic.
                        let types = vec![LType::Unknown; next_stack];
                        let ctx = Rc::new(Context::new(types));
                        self.versions.entry(lclos.ro(owner).prototype).or_insert_with(|| HashMap::default());
                        self.set_current(lclos.clone());
                        let block = self.version(owner, 0, ctx);
                        debug!("{:?} {block:?}", self.blocks);
                        self.set_current(lclos.clone());
                        id = block;
                        off = 0;
                        continue;
                    } else if let LValue::NClosure(ncall) = to_call {
                        let nf = ncall.native();
                        gc.publish(&state, &*self);
                        state.call_native(nf, a as u16, b, c, owner);
                        // FIXME(metatables): __call
                    } else {
                        panic!("cant call {:?}", to_call);
                    }
                },
                Residual::Jump(target) => {
                    id = target;
                    off = 0;
                },
                Residual::Thunk(thunk) => {
                    debug!("thunk {:?}", &thunk);
                    (thunk.0.borrow_mut())(self, owner, &mut state, off)
                },
                Residual::Ret(pc, a, b) => {
                    debug!("spec final blocks: {:?}", self.blocks);
                    match state.do_return(owner, a as usize, b as usize) {
                        Ok(ReturnLocation::Interpreter(caller)) => {
                            state.pc = caller;
                            return (state, None);
                        },
                        Ok(ReturnLocation::Generator(block, disp)) => {
                            self.set_current(state.clos.clone());
                            id = block;
                            off = disp;
                        },
                        Err(r_vals) => {
                            return (state, Some(r_vals));
                        },
                    }
                },
                Residual::GC => {
                    off += 1;
                    // GC safepoint. See Note [GC roots].
                    // SAFETY: We have no stack owned objects, and all previous residual
                    // operations must have either dropped their objects or published them
                    // to RunState for them to be accessed after this.
                    unsafe { gc.step(&state, &*self, owner); }
                },
            }
        }
    }

    // TODO: this is gross! if we spec a block we have to switch current, but then forcing a thunk
    // from another function may at runtime use the wrong current closure. figure out some better
    // way (worse case each block has its own closure and we switch in run when we enter...)
    pub fn set_current(&mut self, clos: Tc<LClosure<'src, 'intern>>) {
        self.clos = clos;
    }

    pub fn count(&self) -> usize {
        let mut count = 0;
        for (proto, versions) in &self.versions {
            for version in versions {
                count += self.blocks[version.1.0].instructions.len();
            }
        }
        count
    }

    pub fn dump(&self, owner: &Owner, proto: LProto<'src, 'intern>, filepath: &str) {
        use graphviz_rust::*;
        use graphviz_rust::printer::*;
        use graphviz_rust::cmd::*;
        use dot_structures::*;
        use dot_generator::*;

        let Some(versions) = self.versions.get(&proto) else { return; };
        let mut reverse_versions = HashMap::new();
        for (k, v) in versions.iter() {
            reverse_versions.insert(v.0, k);
        }

        let g = graph!(strict di id!("t"); subgraph!("s",
            self.blocks.iter().enumerate().flat_map(|(id, residuals)| {
                let block_id = id;
                let mut instructions = Vec::new();
                let mut edges = vec![];

                fn safe_str(s: impl Into<String>) -> String {
                    let s = s.into().replace("<", "\\<");
                    let s = s.replace(">", "\\>");
                    s
                }

                for (off, res) in residuals.instructions.iter().enumerate() {
                    let inst_label = res.to_string();
                    instructions.push(inst_label);
                    match res {
                        Residual::Jump(target) => {
                            edges.push(Stmt::Edge(edge!(node_id!(block_id) => node_id!(target.0))));
                        }
                        Residual::NativeCall { nf, a, b, c }  => {
                            edges.push(Stmt::Edge(edge!(node_id!(block_id) => node_id!(format!("\"{:p}\"", nf)); attr!("label", "ncall"))));
                        },
                        Residual::Guard { .. } | Residual::GuardDynamic(_) | Residual::HashGuard { .. } | Residual::NativeGuard { .. } | Residual::LuaGuard { .. } => {
                            if let Some(Residual::Jump(target)) = residuals.instructions.get(off + 2) {
                                edges.push(Stmt::Edge(edge!(node_id!(block_id) => node_id!(target.0); attr!("label", "pass"))));
                            }
                            if let Some(Residual::Jump(target)) = residuals.instructions.get(off + 1) {
                                edges.push(Stmt::Edge(edge!(node_id!(block_id) => node_id!(target.0); attr!("label", "fail"))));
                            }
                        },
                        Residual::Select(targets) => {
                            for (name, target) in targets {
                                edges.push(Stmt::Edge(
                                    edge!(node_id!(block_id) => node_id!(target.0); attr!("label", name))));
                            }
                        },
                        _ => {}
                    }
                }
                debug!("graphviz edges: {:?}", edges);

                let context_str = if let Some((subpc, ctx)) = reverse_versions.get(&block_id) {
                    format!("PC: {:?}\\n{} |", subpc, ctx.tostring(owner))
                } else {
                    "".to_string()
                };
                let context_str = context_str.replace("{", "(");
                let context_str = context_str.replace("}", ")");

                //let label = safe_str(format!("\"{} | {{ {} {} }}\"", block_id, context_str, instructions));
                #[cfg(feature = "graph")]
                let entered = format!(" x{}", residuals.entered);
                #[cfg(not(feature = "graph"))]
                let entered = "";
                let label = safe_str(format!("\"{}{} | {{ {} {} }}\"", block_id, entered, context_str, instructions.drain(..).intersperse("| ".to_string()).collect::<String>()));

                let mut stmts = vec![Stmt::Node(node!(block_id;
                    attr!("id", block_id),
                    attr!("shape", "record"),
                    attr!("label", label)
                ))];
                stmts.extend(edges);
                stmts
            }).collect::<Vec<_>>()
          )
        );

        // The DOT source is written next to the rendered graph, to read as text.
        let dot_path = std::path::Path::new(filepath).with_extension("dot");
        std::fs::write(&dot_path, g.print(&mut PrinterContext::default()))
            .unwrap_or_else(|e| panic!("writing {}: {e}", dot_path.display()));
        let graph_out = exec(g, &mut PrinterContext::default(), vec![
            CommandArg::Format(Format::Pdf),
            CommandArg::Output(filepath.to_string()),
        ]).unwrap_or_else(|e| panic!("rendering {filepath} with graphviz `dot`: {e}"));
        debug!("graphviz output: {}", graph_out);
    }
}
