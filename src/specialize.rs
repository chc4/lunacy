#![allow(unused_variables, unused_assignments, unused)]

use std::borrow::Cow;
use std::collections::{HashMap, VecDeque};
use std::ops::{Coroutine, CoroutineState, Deref};
use std::pin::Pin;
use std::rc::Rc;
use std::cell::{Cell, RefCell};

use crate::vm::{CallstackEntry, HashWitness, NClosure, NativeFunc, Opcode, Location, Return, Upvalue};
use crate::classes::{ClassFact, Label, Loc, Root, Target};
use qcell::{LCell, LCellOwner};
use crate::{Owner, TLCell, TlcOwner};
use crate::vm::{Tc, Vm};
use crate::vm::{BlockId, HashRef, Place};
use crate::vm::{LClosure, LProto};
use crate::vm::{LValue, LType, Number, Table, FVec, LBoxed, LCanon, IStr};
use crate::lboxed::is_integer;
use crate::vm::{InstructionDecode, Unpacker};
use crate::vm::RunState;
use crate::vm::LConstant;
use crate::vm::InternedHasher;
use crate::chunk::Constant;
use crate::chunk::Instruction;
use crate::window::{windowed, Access, Window};
// The native code generator (`JitContext`) and its per-block `JitInfo` (dynasm
// buffer + hotness tiering) are only needed with the `jit` feature.
#[cfg(feature = "jit")]
use crate::jit::{JitInfo, JitContext};
use crate::gc::{Mark, Heap, GcCtx};

use crate::{debug, info, warn};
use smallvec::SmallVec;

use crate::generators::*;

impl<'src, 'intern> LValue<'src, 'intern> {
    /// Get the LType of an observed value
    pub fn typeof_(&self) -> LType {
        match self {
            LValue::Integer(_) => LType::Integer,
            LValue::Double(_) => LType::Double,
            LValue::InternedString(_) | LValue::OwnedString(_) => LType::String,
            LValue::Table(t) => LType::Table,
            LValue::LClosure(_) | LValue::NClosure(_) => LType::Closure,
            LValue::Nil => LType::Nil,
            LValue::Bool(_) => LType::Bool,
            LValue::Userdata(_) => LType::Userdata,
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
    /// The bytecode PC the block starts at, or the PC a
    /// block starting inside an instruction belongs to.
    pub pc: Pc,
    /// Whether the block may have allocated since its last GC safepoint, which
    /// it then gets at its end. See Note [Block safepoints].
    allocates: bool,
    /// A version of a pc's context, which jumps to it enter. See Note [Version
    /// compatibility].
    context: Option<Rc<Context>>,
    /// The upvalue cells holding their upvalue's value whenever the block is entered, by
    /// `cell` index: every cell where its context isn't known. See Note [Upvalue cells].
    pub cells: u32,
    /// The promoted values its context has, which the JIT's notes show. See Note [Promoted values].
    pub promoted: SmallVec<[(Pc, i32); 2]>,
    /// The function whose code it is, which needn't be the running frame's: an inlined call's
    /// frame isn't made until something observes it. See Note [Peephole fusion] in `peephole`.
    pub proto: usize,
    #[cfg(feature = "jit")]
    pub jit_info: JitInfo,
    /// Times the interpreter entered the block, shown by `dump`.
    #[cfg(feature = "graph")]
    pub entered: u64,
}

// Note [Block safepoints]
// ~~~~~~~~~~~~~~~~~~~~~~~
// The collector steps only at safepoints (`Residual::GC`), so any code that allocates must reach
// one, or a loop allocating only there never collects. Emitter coroutines say an operation
// allocates with `YieldOp::CollectGarbage`; native calls are pessimistically considered to
// allocate as well. Known Lua call target aren't required to be considered allocations, because
// the target function will itself have ran its own safepoint before returning.
// Requiring GC doesn't immediately emit a safepoint but instead marks the block, which gets one
// safepoint before any exit. This allows multiple GC-requiring operations inside one block to only
// require a single safepoint, which is an optimization as each safepoint requires flushing the
// JIT's register window, and a block's allocations are few enough to wait for its end.

impl Block {
    fn new(pc: Pc) -> Self {
        Self {
            instructions: vec![],
            pc,
            allocates: false,
            context: None,
            cells: u32::MAX,
            promoted: SmallVec::new(),
            proto: 0,
            #[cfg(feature = "jit")]
            jit_info: JitInfo::new(),
            #[cfg(feature = "graph")]
            entered: 0,
        }
    }
}

// With feature `unreachable`, `unreachable!` is unchecked. Its message is unused.
#[cfg(feature = "unreachable")]
#[macro_export]
macro_rules! unreachable {
    ($($message:tt)*) => { unsafe { core::hint::unreachable_unchecked() } }
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
    /// The slots it writes, if it says: else any. See Note [Fragile information].
    pub writes: Option<Vec<usize>>,
    /// Whether it reads the frame it runs in past its slots: its closure, the callstack, or the
    /// top. See Note [Peephole fusion] in `peephole`.
    pub frame: bool,
}

/// A residual as the graph and window dumps label it.
impl std::fmt::Display for Residual {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Residual::Guard { idx, expected } => write!(f, "guard({}, {})", idx, expected),
            Residual::NumericGuard { idx, expected } => write!(f, "numeric_guard({}, {})", idx, expected),
            Residual::NativeGuard { idx, ptr } => write!(f, "native_guard({}, {:p})", idx, *ptr),
            Residual::LuaGuard { idx, ptr } => write!(f, "lua_guard({}, {:p})", idx, *ptr),
            Residual::Exec(ResidualExec { name, .. }) => write!(f, "exec({})", name),
            Residual::ExecWindow(w) => write!(f, "window({})", window_label(&**w)),
            Residual::GuardDynamic(w) => write!(f, "guard_dynamic({})", window_label(&**w)),
            Residual::Jump(target) => write!(f, "jump({})", target.0),
            Residual::PatchableJump(target) => write!(f, "patchable_jump({})", target.0),
            Residual::Call { a, b, c } => write!(f, "call({}, {}, {})", a, b, c),
            Residual::Arrive { a, c } => write!(f, "arrive({}, {})", a, c),
            Residual::ReturnedFrom(from) => write!(f, "returned({}, {:#x})", from & UNKNOWN_RETURN as u64, (from & 0xffff_ffff) >> crate::vm::EFFECTS_SHIFT),
            Residual::Arrived { a, c, returned } => write!(f, "arrived({}, {}, {})", a, c, returned),
            Residual::NativeCall { nf, a, b, c } => write!(f, "ncall({:p}, {}, {}, {})", nf, a, b, c),
            Residual::LuaCall { entry: CallEntry::Block(block), a, b, c, .. } => write!(f, "lcall({}, {}, {}, {})", block.0, a, b, c),
            Residual::LuaCall { entry: CallEntry::Context(_), a, b, c, .. } => write!(f, "lcall(?, {}, {}, {})", a, b, c),
            Residual::TailCall { entry: CallEntry::Block(block), a, b, .. } => write!(f, "tcall({}, {}, {})", block.0, a, b),
            Residual::TailCall { entry: CallEntry::Context(_), a, b, .. } => write!(f, "tcall(?, {}, {})", a, b),
            Residual::HashGuard { tab, href, expected, .. } => write!(f, "hguard({}, {:?}, {})", tab, href, expected),
            Residual::GuardWitness { href, expected } => write!(f, "guard_witness({:?}, {})", href, expected),
            Residual::EpochCheck { tab, href, place } => write!(f, "epoch({}, {:?}, {:?})", tab, href, place),
            Residual::Thunk(_) => write!(f, "thunk"),
            Residual::Tripped(of) => write!(f, "tripped({of:?})"),
            Residual::Select(targets) => write!(f, "select"),
            Residual::Branch { .. } => write!(f, "branch"),
            Residual::Ret(..) => write!(f, "ret"),
            Residual::Inline { a, b, .. } => write!(f, "inline({}, {})", a, b),
            Residual::InlineReturn { a, b, .. } => write!(f, "inline_ret({}, {})", a, b),
            Residual::Enter(by) => write!(f, "enter({by})"),
            Residual::Leave(by) => write!(f, "leave({by})"),
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
        Self { name, body, template: None, writes: None, frame: false }
    }

    /// One reading the frame it runs in past its slots. See `frame`.
    pub fn framed(name: &'static str, body: Rc<dyn for <'a, 'b, 'src, 'intern> Fn(&mut Owner, &'b mut RunState<'src, 'intern>)>) -> Self {
        Self { frame: true, ..Self::new(name, body) }
    }

    /// It, saying it writes only the slots `slots`.
    pub fn writing(mut self, slots: &[usize]) -> Self {
        self.writes = Some(slots.to_vec());
        self
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

/// A native's generator, of an opcode's generator's type, boxed: a native's call is compiled by
/// it as an opcode is by its own. See Note [Native generators] in `library`.
pub trait NativeGen: Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Unpin {
    fn clone_box(&self) -> Box<dyn NativeGen>;
}

impl<C: Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static> NativeGen for C {
    fn clone_box(&self) -> Box<dyn NativeGen> {
        Box::new(self.clone())
    }
}

impl Clone for Box<dyn NativeGen> {
    fn clone(&self) -> Self {
        (**self).clone_box()
    }
}

/// The coroutine compiling code: a generator, run by the peephole, which holds what it can of what
/// the generator yields and yields the rest, laying out first what that needs of what it holds.
/// What it holds is suspended with it, in whatever suspends it. See Note [Peephole fusion] in
/// `peephole`.
#[derive(Clone)]
pub struct Gen {
    inner: Box<dyn NativeGen>,
    /// What it holds.
    held: crate::peephole::Spells,
    /// What the code is compiled in, as of its last resumption: what is known of values, and the
    /// function.
    ctx: Option<Rc<Context>>,
    proto: Option<LProto<'static, 'static>>,
    /// The instruction its generator compiles, and whether it may hold its operations: not those
    /// of one an exit runs again.
    at: Pc,
    holds: bool,
    /// Whether it holds nothing ever: its code jumps to a version after it.
    pub unheld: bool,
    /// What it yields before resuming the generator.
    out: VecDeque<YieldOp>,
    /// What it resumes the generator with, where it answered the generator itself; else the
    /// generator gets the answer to the last of `out`, its yield passed on.
    next: Option<ResumeArg>,
    /// The yield passed on last, which laying everything out passes on again.
    last: Option<YieldOp>,
    /// The integer op, or table access, the window the generator yields next is.
    described: Option<crate::peephole::IntOp>,
    memory: Option<crate::peephole::MemOp>,
    /// What the instruction's generator returned, as the peephole asks for the next's.
    done: Option<ResumeArg>,
    /// The jump's target the peephole asked to go on at, straight on, and whether it looks ahead
    /// at the jump it's at.
    continuing: Option<Pc>,
    looked: bool,
}

impl Gen {
    pub fn boxed(inner: impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static) -> Box<Gen> {
        Self::of(Box::new(inner))
    }

    pub fn of(inner: Box<dyn NativeGen>) -> Box<Gen> {
        Box::new(Gen {
            inner,
            held: Default::default(),
            ctx: None,
            proto: None,
            at: 0,
            holds: false,
            unheld: false,
            out: VecDeque::new(),
            next: None,
            last: None,
            described: None,
            memory: None,
            done: None,
            continuing: None,
            looked: false,
        })
    }

    /// `inner`, a generator boxed, run holding `held`.
    pub fn holding_of(held: crate::peephole::Spells, inner: Box<dyn NativeGen>) -> Box<Gen> {
        let mut holding = Self::of(inner);
        holding.held = held;
        holding
    }

    /// Go on with the next instruction's generator, `inner`, holding what it holds: its answer to
    /// `NextPc`. See Note [Peephole fusion] in `peephole`.
    pub fn next_instruction(&mut self, inner: Box<dyn NativeGen>) {
        self.inner = inner;
    }

    /// `inner`, run holding `held`.
    pub fn holding(held: crate::peephole::Spells, inner: impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static) -> Box<Gen> {
        let mut holding = Self::boxed(inner);
        holding.held = held;
        holding
    }

    /// Whether it holds anything: code compiled from it then is its own, never a version's, as
    /// what it holds isn't in the context.
    pub fn holds_any(&self) -> bool {
        !self.held.is_empty()
    }

    /// What it holds, which the next instruction's generator is run holding.
    pub fn take_held(&mut self) -> crate::peephole::Spells {
        std::mem::take(&mut self.held)
    }

    /// What `yielded` needs of the frames of the inlined calls the code is in: made, if it may
    /// observe them; else their base moved to, if it may lay out code naming their slots. See Note
    /// [Peephole fusion] in `peephole`.
    fn frames_for(&mut self, yielded: &YieldOp) {
        let Some(ctx) = self.ctx.as_ref() else { return };
        if ctx.inline.iter().all(|frame| frame.made == Made::Yes) {
            return;
        }
        if self.observes(yielded) {
            for frame in &mut Rc::make_mut(self.ctx.as_mut().unwrap()).inline {
                frame.made = Made::Yes;
            }
            self.out.push_back(YieldOp::MakeFrames);
        } else if self.lays_out(yielded) {
            self.enter();
        }
    }

    /// Move the base to the frames of the inlined calls the code is in, if it isn't, before code
    /// naming their slots is laid out.
    fn enter(&mut self) {
        let Some(ctx) = self.ctx.as_mut() else { return };
        // A frame its call passed what's up to the top is made: what it was passed is found only
        // then.
        if ctx.inline.iter().any(|frame| frame.made == Made::No && frame.b == 0) {
            for frame in &mut Rc::make_mut(ctx).inline {
                frame.made = Made::Yes;
            }
            self.out.push_back(YieldOp::MakeFrames);
            return;
        }
        if ctx.inline.iter().any(|frame| frame.made == Made::No) {
            for frame in Rc::make_mut(ctx).inline.iter_mut().filter(|frame| frame.made == Made::No) {
                frame.made = Made::Base;
            }
            self.out.push_back(YieldOp::Enter);
        }
    }

    /// The slots `yielded` may lay out code reading, if it says: else any.
    fn slots_read(&self, yielded: &YieldOp) -> Option<Vec<usize>> {
        let reading = |w: &Rc<dyn Window>| w.operands().iter().zip(w.accesses()).filter(|(_, a)| a.reads()).map(|(s, _)| *s).collect();
        Some(match yielded {
            YieldOp::ExecWindow(w) | YieldOp::OptimisticExec(w) | YieldOp::GuardDynamic(w) => reading(w),
            YieldOp::Guard(idx, _) | YieldOp::Narrow(idx) | YieldOp::Promote(idx) | YieldOp::Trip(Some(idx)) => vec![*idx],
            YieldOp::GuardRk(rk, _) | YieldOp::GuardCType(rk, _) => if rk & 0x100 != 0 { Vec::new() } else { vec![*rk] },
            YieldOp::Trip(None) => Vec::new(),
            // Asking what the context knows of a table's keys reads it, and the key.
            YieldOp::HashKey(slot, key, _) => [*slot].into_iter().chain((*key & 0x100 == 0).then_some(*key)).collect(),
            YieldOp::LoadUpvalue(..) | YieldOp::UpvalueKnown(_) | YieldOp::UpvalueCell(_) | YieldOp::UpvalueHolds(..)
                | YieldOp::FrameUnmade | YieldOp::HoldsValue(..) => Vec::new(),
            // Decided as it compiles while it holds anything, reading no slot. See Note [Optimistic
            // ops].
            YieldOp::Encoding(_) if self.holds_any() => Vec::new(),
            yielded if !self.lays_out(yielded) => Vec::new(),
            _ => return None,
        })
    }

    /// Whether `yielded` may lay out code reading the frame it runs in past the slots it names: its
    /// closure, the callstack, or the top, or an upvalue's value a guard finds. See Note [Peephole
    /// fusion] in `peephole`.
    fn observes(&self, yielded: &YieldOp) -> bool {
        let ctx = self.ctx.as_ref().expect("a generator run in a context");
        let upvalue = |slot: usize| ctx.values.members(Loc::root(Root::Slot(slot as u16))).into_iter().any(|root| matches!(root, Root::Upvalue(_)));
        match yielded {
            YieldOp::Exec(func) => func.frame,
            YieldOp::ExecWindow(w) | YieldOp::OptimisticExec(w) | YieldOp::GuardDynamic(w) => w.closure(),
            YieldOp::Call(_) | YieldOp::CallResume(_) | YieldOp::NativeCall { .. } | YieldOp::CollectGarbage => true,
            YieldOp::Guard(idx, _) => upvalue(*idx),
            YieldOp::GuardRk(rk, _) | YieldOp::GuardCType(rk, _) => rk & 0x100 == 0 && upvalue(*rk),
            _ => false,
        }
    }

    /// Whether `yielded` may lay out code, or only asks of or tells the context. See Note [Peephole
    /// fusion] in `peephole`.
    fn lays_out(&self, yielded: &YieldOp) -> bool {
        let ctx = self.ctx.as_ref().expect("a generator run in a context");
        let known = |slot: usize, expected: &CType| {
            let found = &ctx.types[slot];
            expected.accepts(found) || !found.accepts(expected)
        };
        !match yielded {
            YieldOp::Typeof(_) | YieldOp::TypeofRk(_) | YieldOp::TypeofK(_) | YieldOp::IntegerK(_) | YieldOp::IntegralK(_)
                | YieldOp::NumberK(_) | YieldOp::BoxedK(_) | YieldOp::SetTypes(_) | YieldOp::SetCTypes(_) | YieldOp::Decided(_)
                | YieldOp::Effect(_) | YieldOp::EncodeK(..) | YieldOp::HoldsK(..) | YieldOp::IsKey(..)
                | YieldOp::Subject(_) | YieldOp::ArrayKind(_) | YieldOp::IsElementOf(..) | YieldOp::ArrayType(..)
                | YieldOp::FrozenElement(..) | YieldOp::Discovered(..) | YieldOp::ValueOf(_) | YieldOp::NativeWindowArgs(..)
                | YieldOp::Uniques(_) | YieldOp::Unique(_) | YieldOp::Copy(..) | YieldOp::Clobber(_) | YieldOp::Took | YieldOp::Holding { .. } | YieldOp::Created(_) => true,
            YieldOp::Narrow(slot) => ctx.types[*slot] != CType::Type(LType::Double),
            YieldOp::Guard(idx, expected) => known(*idx, &CType::Type(*expected)),
            YieldOp::GuardRk(rk, expected) => rk & 0x100 != 0 || known(*rk, &CType::Type(*expected)),
            YieldOp::GuardCType(rk, expected) => rk & 0x100 != 0 || known(*rk, expected),
            _ => false,
        }
    }

    /// It, as an exit going on from where it was goes on: what it held written, nothing held.
    pub fn forgetting(&self) -> Box<Gen> {
        let mut again = Box::new(self.clone());
        again.held = Default::default();
        again.out.clear();
        again
    }

    /// What it sees of the code it compiles, before it is resumed.
    fn see(&mut self, ctx: &Rc<Context>, proto: LProto, instruction: Option<(Pc, bool)>) {
        self.ctx = Some(ctx.clone());
        self.proto = Some(proto as LProto<'static, 'static>);
        (self.at, self.holds) = instruction.unwrap_or((self.at, false));
        self.holds &= !self.unheld;
    }

    /// Go on running `inner` in place of its generator, holding what it holds: a native's
    /// generator, compiling its call.
    pub fn generate(&mut self, inner: Box<dyn NativeGen>) {
        self.inner = inner;
        self.next = Some(ResumeArg::Start);
        self.last = None;
        self.described = None;
        self.memory = None;
    }

    /// What it knows of `slot`'s constant value.
    fn constant(&self, slot: usize) -> Option<i32> {
        match self.ctx.as_ref()?.values.fact(Loc::root(Root::Slot(slot as u16)), CONSTANT) {
            Some(Known::Constant { value, .. }) => Some(*value),
            _ => None,
        }
    }

    /// Lay out what an op needing `need` needs of what it holds (everything without one), about
    /// to write `stale`. See Note [Peephole fusion] in `peephole`.
    fn lay_out(&mut self, need: Option<crate::peephole::Need>, stale: &[usize], _trigger: &str) {
        let all = std::mem::take(&mut self.held);
        let (laid, kept) = match &need {
            Some(need) => all.split(need),
            None => (all, crate::peephole::Spells::default()),
        };
        if laid.is_empty() {
            self.held = kept;
            return;
        }
        self.enter();
        let ops = laid.lay_out(self.at, &kept);
        #[cfg(feature = "tracing")]
        self.out.push_back(YieldOp::PeepholeTrace("lay_out", vec![
            ("trigger", _trigger.to_string()),
            ("stores", laid.stores.len().to_string()),
            ("spells", laid.spells.len().to_string()),
            ("windows", ops.iter().map(|laid| laid.op.name()).collect::<Vec<_>>().join(" ")),
            ("kept", (kept.stores.len() + kept.spells.len()).to_string()),
        ]));
        for laid in ops {
            if laid.checked {
                let unknown = laid.unknown.iter().chain(stale).copied().collect();
                self.out.push_back(YieldOp::Fused { op: laid.op, exit: laid.exit, unknown });
            } else {
                self.out.push_back(YieldOp::LaidOut(laid.op));
            }
        }
        self.held = kept;
    }

    /// Whether `yielded` leaves what it holds held, laying out no code: with the window after
    /// `described` or `memory` if they say, which it is offered.
    fn passes(&self, yielded: &YieldOp, described: Option<&crate::peephole::IntOp>, memory: Option<&crate::peephole::MemOp>) -> bool {
        let ctx = self.ctx.as_ref().expect("a generator run in a context");
        let held = &self.held;
        let at = self.at;
        let known = |slot: usize, expected: &CType| {
            let found = &ctx.types[slot];
            expected.accepts(found) || !found.accepts(expected)
        };
        match yielded {
            YieldOp::Typeof(_) | YieldOp::TypeofRk(_) | YieldOp::TypeofK(_) | YieldOp::IntegerK(_) | YieldOp::IntegralK(_)
                | YieldOp::NumberK(_) | YieldOp::BoxedK(_) | YieldOp::SetTypes(_) | YieldOp::SetCTypes(_) | YieldOp::Decided(_)
                | YieldOp::Encoding(_) | YieldOp::Effect(_) | YieldOp::IntegerOp(_) | YieldOp::MemoryOp(_)
                | YieldOp::EncodeK(..) | YieldOp::HoldsK(..) | YieldOp::Created(_) | YieldOp::Copy(..)
                | YieldOp::Uniques(_) | YieldOp::Unique(_) => true,
            // What the context knows of upvalues, and is told of them: no code.
            YieldOp::LoadUpvalue(..) | YieldOp::UpvalueKnown(_) | YieldOp::UpvalueCell(_) | YieldOp::UpvalueHolds(..)
                | YieldOp::Captures(..) | YieldOp::Close(_) => true,
            // Slots whose values are dead: what spells write there is never read, if none reads them.
            YieldOp::Clobber(from) => held.inputs().all(|slot| slot < *from),
            YieldOp::OptimisticExec(_) => described.is_some(),
            // An access it is told of holds them as it touches memory. See Note [Peephole memory]
            // in `peephole`.
            YieldOp::ExecWindow(window) => described.is_some() || (memory.is_some() && held.off_registers(&**window))
                || held.untouched(&**window),
            // Its check reads only whether the table is watched.
            YieldOp::Trip(of) => of.is_none_or(|slot| held.spells.iter().all(|spell| spell.dest != slot)),
            // One joining a spell, or, as a type guard found out at runtime, one reading neither
            // what they hold nor memory a held store may change.
            YieldOp::GuardDynamic(test) => held.joins_guard(&**test, at) || held.across_guard(&**test, at),
            // What a get or set asks before its guard on the key, and what a load learns of its
            // register.
            YieldOp::Subject(_) | YieldOp::ArrayKind(_) | YieldOp::IsElementOf(..) | YieldOp::ArrayType(..) => true,
            // What a load from a frozen table, or a test, asks of what the context knows, and
            // what it learns of the register the load writes. See Note [Frozen tables].
            YieldOp::FrozenElement(..) | YieldOp::Discovered(..) | YieldOp::ValueOf(_) => true,
            // What a call asks of a native it may make a window op.
            YieldOp::NativeWindowArgs(..) => true,
            // A call's thunk holds them: into its callee's code, or laid out before a call. See
            // Note [Peephole fusion] in `peephole`.
            // A known native without a generator is laid out here, observing them.
            YieldOp::Call(CallTarget::Dynamic(a, _, _)) => held.spells.iter().all(|spell| spell.dest != *a && spell.at != at)
                && match &ctx.types[*a] {
                    CType::NativeFunction(nf) => !nf.is_protected_call() && nf.generator().is_some(),
                    _ => true,
                },
            // A field's key is no element: what it lays out reads and writes hash parts, of
            // tables no held spell writes the register of. See Note [Peephole memory] in
            // `peephole`.
            YieldOp::HashKey(slot, key, _) => held.spells.iter().all(|spell| spell.dest != *slot && (key & 0x100 != 0 || spell.dest != *key)),
            YieldOp::Narrow(slot) => ctx.types[*slot] != CType::Type(LType::Double),
            // One found out at runtime keeps them held on its ways, if it reads none and none
            // holds its instruction's operations, which a restart past it would run again.
            YieldOp::Guard(idx, expected) => known(*idx, &CType::Type(*expected))
                || held.spells.iter().all(|spell| spell.dest != *idx && spell.at != at),
            YieldOp::GuardRk(rk, expected) => rk & 0x100 != 0 || known(*rk, &CType::Type(*expected)),
            YieldOp::GuardCType(rk, expected) => rk & 0x100 != 0 || known(*rk, expected),
            // Of a value the context knows: no code; else its thunk holds them, guarding only the
            // slot. See Note [Promoted values].
            YieldOp::Promote(slot) => ctx.constant(*slot).is_some() || held.spells.iter().all(|spell| spell.dest != *slot && spell.at != at),
            _ => false,
        }
    }

    /// Hold integer op `op`, of `window`, laying out first what it must of what it holds; whether
    /// it did. See Note [Peephole fusion] in `peephole`.
    fn hold(&mut self, op: crate::peephole::IntOp, window: &Rc<dyn Window>, optimistic: bool) -> bool {
        use crate::peephole::{Need, Offer};
        if !crate::peephole::fuses() || !self.holds {
            return false;
        }
        let ctx = self.ctx.clone().expect("a generator run in a context");
        let known = |slot: usize| match ctx.values.fact(Loc::root(Root::Slot(slot as u16)), CONSTANT) {
            Some(Known::Constant { value, .. }) => Some(*value),
            _ => None,
        };
        let trigger = format!("window {}", window.name());
        let mut folded = None;
        // What it needs laid out, as witchcraft's invariants have it, then everything, then
        // nothing held: offered again after each.
        let mut laid = 0;
        let held = loop {
            match self.held.offer(&op, self.at, known) {
                Offer::Held => break true,
                Offer::Folded(value) => {
                    folded = Some(value);
                    break true;
                },
                Offer::Flush | Offer::Refused if !self.held.is_empty() && laid < 2 => {
                    let need = (laid == 0).then(|| Need { reads: op.reads().collect(), writes: vec![op.dest], memory: false });
                    self.lay_out(need, &[op.dest], &trigger);
                    laid += 1;
                },
                _ => break false,
            }
        };
        if !held {
            return false;
        }
        let writes = window.operands().iter().zip(window.accesses()).filter(|(_, a)| a.writes()).map(|(s, _)| *s).collect();
        // A constant loaded, of no slot, is known as its load makes it known.
        let constant = folded.filter(|_| op.reads().next().is_some()).map(|value| (op.dest, value));
        self.out.push_back(YieldOp::Holding { writes, reads: op.reads().collect(), constant, optimistic });
        self.next = Some(if optimistic { ResumeArg::Matched } else { ResumeArg::Start });
        true
    }

    /// Table access `op`, of `window`: a store held, or a load of an element a held store is into
    /// its value, or after the held stores that may be into it. Whether it took it. See Note
    /// [Peephole memory] in `peephole`.
    fn access(&mut self, op: crate::peephole::MemOp, window: &Rc<dyn Window>) -> bool {
        use crate::peephole::{Load, MemOp, Stored};
        let ctx = self.ctx.clone().expect("a generator run in a context");
        let alias = |a, b| cells(&ctx, a, b);
        match op {
            MemOp::Store { cell, value } if crate::peephole::fuses() && self.holds => {
                let _dead = self.held.hold_store(cell, value, window.clone(), self.at, alias);
                #[cfg(feature = "tracing")]
                self.out.push_back(YieldOp::PeepholeTrace("store", vec![("element", format!("{cell:?}")), ("value", format!("{value:?}")), ("dead", _dead.to_string())]));
            },
            MemOp::Load { cell, dest } if !self.held.stores.is_empty() => {
                let outcome = self.held.load(cell, alias);
                #[cfg(feature = "tracing")]
                self.out.push_back(YieldOp::PeepholeTrace("load", vec![("element", format!("{cell:?}")), ("outcome", match &outcome {
                    Load::Forward(value) => format!("forward {value:?}"),
                    Load::After(stores) => format!("after {}", stores.len()),
                })]));
                let load = match outcome {
                    Load::Forward(Stored::Slot(slot)) => Rc::new(crate::generators::Move::new(&[slot, dest])) as Rc<dyn Window>,
                    Load::Forward(Stored::Boxed(bits)) => Rc::new(crate::generators::LoadStored::new(bits, &[dest])),
                    Load::After(stores) => {
                        self.out.extend(stores.into_iter().map(YieldOp::ExecWindow));
                        window.clone()
                    },
                };
                self.out.push_back(YieldOp::ExecWindow(load));
            },
            _ => return false,
        }
        self.next = Some(ResumeArg::Start);
        true
    }

    /// Take the generator's `yielded`: hold it, or answer it, or pass it on, laying out what it
    /// needs first.
    fn take(&mut self, yielded: YieldOp) {
        use crate::peephole::{MemOp, Need};
        // A jump that is the only way on, its generator's next yield a jump to its target, goes on
        // at the target holding what it holds: the target is straight on, no block's. See Note
        // [Peephole fusion] in `peephole`.
        if let YieldOp::GetBlock(target) = yielded && !std::mem::take(&mut self.looked) && self.holds_any() {
            const AHEAD: BlockId = BlockId(usize::MAX);
            let mut ahead = self.inner.clone();
            if let CoroutineState::Yielded(YieldOp::Jump(AHEAD)) = Pin::new(&mut *ahead).resume(ResumeArg::BlockId(AHEAD)) {
                self.continuing = Some(target);
                self.out.push_back(YieldOp::Continue(target));
                return;
            }
        }
        match yielded {
            // Of how much of the frame the code is in is made.
            YieldOp::FrameUnmade => {
                let ctx = self.ctx.as_ref().expect("a generator run in a context");
                let called = ctx.inline.last().filter(|frame| frame.made != Made::Yes).and_then(|frame| frame.closure);
                self.next = Some(called.map_or(ResumeArg::Failed, ResumeArg::Boxed));
                return;
            },
            // Of what the code holds where: a slot holding what it would be moved, which no spell
            // writes, holds it.
            YieldOp::HoldsValue(dest, src) => {
                let ctx = self.ctx.as_ref().expect("a generator run in a context");
                let unheld = |slot: usize| self.held.spells.iter().all(|spell| spell.dest != slot);
                let holds = dest == src || (unheld(dest) && unheld(src)
                    && ctx.values.members(Loc::root(Root::Slot(src as u16))).contains(&Root::Slot(dest as u16)));
                self.next = Some(if holds { ResumeArg::Matched } else { ResumeArg::Failed });
                return;
            },
            YieldOp::IntegerOp(op) => {
                self.described = Some(op);
                self.next = Some(ResumeArg::Start);
                return;
            },
            YieldOp::MemoryOp(op) => {
                self.memory = Some(op);
                self.next = Some(ResumeArg::Start);
                return;
            },
            _ => {},
        }
        let described = self.described.take();
        let memory = self.memory.take();
        // A store about to run makes held stores into its element dead, laid out first or not.
        // See Note [Peephole memory] in `peephole`.
        if let (Some(MemOp::Store { cell, .. }), YieldOp::ExecWindow(_)) = (&memory, &yielded) {
            let ctx = self.ctx.clone().expect("a generator run in a context");
            let _dead = self.held.kill_stores(*cell, |a, b| cells(&ctx, a, b));
            #[cfg(feature = "tracing")]
            if _dead > 0 {
                self.out.push_back(YieldOp::PeepholeTrace("dead", vec![("element", format!("{cell:?}")), ("dead", _dead.to_string())]));
            }
        }
        // A read of an unset slot gets its nil first, what's held reading the slot as it was laid
        // out before it. See Note [Peephole memory] in `peephole`.
        if !self.held.unset.is_empty() {
            let nils: Vec<usize> = match self.slots_read(&yielded) {
                Some(slots) => self.held.unset.iter().copied().filter(|slot| slots.contains(slot)).collect(),
                None => self.held.unset.clone(),
            };
            if !nils.is_empty() {
                let trigger = match &yielded {
                    YieldOp::ExecWindow(w) | YieldOp::OptimisticExec(w) | YieldOp::GuardDynamic(w) => format!("unset, window {}", w.name()),
                    yielded => format!("unset, {}", format!("{yielded:?}").split(['(', ' ', '{']).next().unwrap_or("")),
                };
                self.lay_out(Some(Need { reads: nils, writes: Vec::new(), memory: false }), &[], &trigger);
            }
        }
        let (writes, reads) = overwrites(&yielded);
        self.held.unset.retain(|slot| !writes.contains(slot));
        // A held store named by a slot about to be written is named by another holding the value.
        if !self.held.stores.is_empty() && !writes.is_empty() {
            let ctx = self.ctx.clone().expect("a generator run in a context");
            rehome(&mut self.held, &ctx, |slot| writes.contains(&slot));
        }
        if !self.held.is_empty() && !self.passes(&yielded, described.as_ref(), memory.as_ref()) {
            // What writes a held value unread: that spell is dead.
            self.held.drop_overwritten(&writes, &reads);
            // A window op with no way out, writing no memory and updating no register in place,
            // which a restart running it again leaves as it was, needs only what it reads, writes,
            // and, reading memory, the stores.
            let need = match &yielded {
                YieldOp::ExecWindow(w) if !w.selects() && !w.accesses().contains(&Access::Update)
                    && matches!(w.memory(), crate::window::Memory::None | crate::window::Memory::Properties | crate::window::Memory::Cells | crate::window::Memory::Fields | crate::window::Memory::Reads) =>
                    // A load described, what it reads of memory as it's held: `access`.
                    Some(Need { reads: reads.clone(), writes: writes.clone(), memory: w.memory() == crate::window::Memory::Reads && memory.is_none() }),
                // A field's key asked, what writes its table's or key's register. See Note [Peephole
                // memory] in `peephole`.
                YieldOp::HashKey(slot, key, _) => Some(Need { reads: [*slot].into_iter().chain((*key & 0x100 == 0).then_some(*key)).collect(), writes: Vec::new(), memory: false }),
                // A guard found out at runtime, as one: what it reads, the rest held across it if
                // they may be. See `Spells::across_guard`.
                YieldOp::GuardDynamic(test) if !test.accesses().contains(&Access::Update)
                    && matches!(test.memory(), crate::window::Memory::None | crate::window::Memory::Properties | crate::window::Memory::Cells | crate::window::Memory::Reads) => {
                    let reads = test.operands().iter().zip(test.accesses()).filter(|(_, a)| a.reads()).map(|(s, _)| *s).collect();
                    Some(Need { reads, writes: Vec::new(), memory: test.memory() == crate::window::Memory::Reads })
                },
                _ => None,
            };
            let trigger = match &yielded {
                YieldOp::ExecWindow(w) | YieldOp::OptimisticExec(w) => format!("window {}", w.name()),
                yielded => format!("{yielded:?}").split(['(', ' ', '{']).next().unwrap_or("").to_string(),
            };
            self.lay_out(need, &writes, &trigger);
            if let YieldOp::GuardDynamic(test) = &yielded && !self.held.is_empty() && !self.held.across_guard(&**test, self.at) {
                self.lay_out(None, &writes, &trigger);
            }
        } else if described.is_none() && matches!(yielded, YieldOp::ExecWindow(_)) {
            // Held across it: what it writes unread is dead.
            self.held.drop_overwritten(&writes, &reads);
        }
        match &yielded {
            YieldOp::ExecWindow(w) if let Some(op) = memory && self.access(op, w) => return,
            YieldOp::ExecWindow(w) | YieldOp::OptimisticExec(w) if let Some(op) = described
                && self.hold(op, w, matches!(yielded, YieldOp::OptimisticExec(_))) => return,
            // A guard joining a held spell: as passed.
            YieldOp::GuardDynamic(test) if self.held.offer_guard(&**test, self.at) => {
                self.out.push_back(YieldOp::Took);
                self.next = Some(ResumeArg::Matched);
                return;
            },
            YieldOp::Clobber(from) => self.held.spells.retain(|spell| spell.dest < *from),
            _ => {},
        }
        self.frames_for(&yielded);
        self.out.push_back(yielded.clone());
        self.last = Some(yielded);
        self.next = None;
    }
}

impl Coroutine<ResumeArg> for Gen {
    type Yield = YieldOp;
    type Return = ResumeArg;

    fn resume(self: Pin<&mut Self>, arg: ResumeArg) -> CoroutineState<YieldOp, ResumeArg> {
        let this = self.get_mut();
        // The specializer's answer to what it yielded last: the generator's, if that was its
        // yield passed on.
        let mut answer = Some(arg);
        loop {
            if let Some(yielded) = this.out.pop_front() {
                return CoroutineState::Yielded(yielded);
            }
            // Its answer to `Continue`: the target's generator, given, or none, where the jump is
            // made as any is.
            if let Some(target) = this.continuing.take() {
                if answer.take() == Some(ResumeArg::Matched) {
                    answer = Some(ResumeArg::Start);
                } else {
                    this.looked = true;
                    this.take(YieldOp::GetBlock(target));
                    continue;
                }
            }
            // Its answer to `NextPc`: the next instruction's generator, given, or none, where the
            // specializer goes on itself.
            if let Some(done) = this.done.take() {
                if answer.take() != Some(ResumeArg::Matched) {
                    return CoroutineState::Complete(done);
                }
                answer = Some(ResumeArg::Start);
            }
            let arg = match this.next.take() {
                Some(own) => own,
                None => answer.take().unwrap_or(ResumeArg::Start),
            };
            answer = None;
            match Pin::new(&mut *this.inner).resume(arg) {
                CoroutineState::Complete(arg) => {
                    this.done = Some(arg);
                    this.out.push_back(YieldOp::NextPc);
                },
                CoroutineState::Yielded(yielded) => this.take(yielded),
            }
        }
    }
}

/// The slots a yield is about to write, and those it reads: a window's, or a constant load's. See
/// Note [Peephole fusion] in `peephole`.
fn overwrites(yielded: &YieldOp) -> (Vec<usize>, Vec<usize>) {
    match yielded {
        YieldOp::ExecWindow(w) | YieldOp::OptimisticExec(w) => {
            let accesses = || w.operands().iter().zip(w.accesses());
            (accesses().filter(|(_, a)| **a == Access::Write).map(|(s, _)| *s).collect(),
             accesses().filter(|(_, a)| a.reads()).map(|(s, _)| *s).collect())
        },
        YieldOp::EncodeK(slot, _) => (vec![*slot], Vec::new()),
        _ => Default::default(),
    }
}

/// A native's generator for its call CALL A B C, given the native itself, for a call of it the
/// generator lays out as any native's (`YieldOp::NativeCall`).
pub type NativeGenerator = fn(crate::vm::NativeFunc, usize, usize, usize) -> Box<dyn NativeGen>;

#[derive(Clone, Debug)]
pub enum YieldOp {
    Typeof(usize), // Resumed with the type of STACK[idx]
    TypeofRk(usize), // Resumed with the type of STACK[idx] or CONSTANT[idx]
    TypeofK(usize), // Resumed with the type of CONSTANT[idx], for an index too wide for an rk
    IntegerK(usize), // Resumed with the value of CONSTANT[idx] as an Integer
    IntegralK(usize), // Resumed with Matched if CONSTANT[idx] is a number an i32 holds exactly,
                      // which a typed op may take as an integer. See Note [Integers]
    NumberK(usize), // Resumed with the value of CONSTANT[idx] as a Number
    BoxedK(usize), // Resumed with the value of CONSTANT[idx], as its Boxed bits
    GetBlock(Pc), // Resumed with the BlockId for calling the given PC with the current types
    GetBlockKeeping(Pc, usize), // As GetBlock, the jump keeping STACK[idx]'s type, which the
                                // instruction jumping wrote
    NativeWindowArgs(usize, usize, usize), // For CALL A B C: resumed with WindowArgs if STACK[A] is
                                           // a native with a window op for the call, else Failed.
                                           // See Note [Native windows]

    Guard(usize, LType), // Resumed with either Matched or Failed if STACK[idx] has the expected
                         // representation
    GuardRk(usize, LType), // Resumed with either Matched or Failed if STACK[idx] or CONSTANT[idx]
                           // has the expected representation
    GuardCType(usize, CType), // Resumed with either Matched or Failed if STACK[idx] or
                              // CONSTANT[idx] is of the expected CType
    GuardDynamic(Rc<dyn Window>), // Resumed with Matched or Failed as the test op passes or fails.
                                  // See Note [Dynamic guards]
    Promote(usize), // Resumed with Integer(v) where STACK[idx], an integer, is guarded equal to v,
                    // the path then promoting v, or Failed where it isn't. See Note [Promoted values]
    OptimisticExec(Rc<dyn Window>), // An op with a cold path, which selects 0 on its hot path and
                                    // 1 on its cold. Resumed with Matched on the hot path, and
                                    // Failed on the cold. See Note [Optimistic ops]
    IntegerOp(crate::peephole::IntOp), // The window yielded next computes this integer op, which the
                                       // peephole may hold. See Note [Peephole fusion] in `peephole`
    Decided(bool), // A guard whose outcome is known, emitting nothing: steps the SubPc as a guard
                   // with that outcome does, for a way meeting ones that take it. Resumed with
                   // Matched or Failed. See Note [Subblocks]

    Exec(ResidualExec), // Emit a residual operation that will be executed
    ExecWindow(Rc<dyn Window>), // Emit a copy&patch window op. See Note [Register window].
    Jump(BlockId), // Emit a jump to the given BlockId
    Call(CallTarget), // Call a block target.
    CallResume(CallTarget), // Call, and then resumed with Start, once the call's results arrive.
    Select(Vec<(&'static str, BlockId)>), // Emit a jump to one of several branches, based on
                                      // `state.select` at runtime

    SetTypes(Vec<(usize, LType)>), // Inform the executor that STACK[idx] = type for each entry
    SetCTypes(Vec<(usize, CType)>), // Inform the executor that STACK[idx] = type for each entry
    Narrow(usize), // Resumed with Matched if STACK[idx] is, or is narrowed to, an integer, else
                   // Failed. See Note [Narrowing]
    WidenConstant(usize), // STACK[idx] is widened to a double if a fact says it holds a
                          // whole constant, else left as it is. See Note [Widening]
    EncodeK(usize, usize), // STACK[idx] is about to be loaded with CONSTANT[k]: resumed with
                           // the double type to load a whole one as a double, Failed as an
                           // integer whose fact isn't introduced, else as an integer. See
                           // Note [Contraction]
    HoldsK(usize, usize), // STACK[idx] was just loaded with CONSTANT[k]. See Note [Widening]
    Versions, // Resumed with Integer, once the code runs: the most versions the running function
              // has at the point of a version the code is reached from. See `jit.versions` in
              // `library`
    Encoding(Fits), // An optimistic integer op is about to be laid out, whose result fits for the
                    // values its operands have if the test does: resumed, once the op first runs,
                    // with the double type to compute it in the double encoding instead, else with
                    // the integer one. See Note [Optimistic ops]
    Clobber(usize), // Inform the executor that every STACK[idx] from idx up is of unknown type
    NativeCall { nf: crate::vm::NativeFunc, a: usize, b: usize, c: usize }, // Emit a call of a pure native, its results from STACK[a] on of unknown type. See Note [Native generators] in `library`.
    ArrayKind(usize), // Resumed with the kind of STACK[idx]'s array part as a Type if the context
                      // knows it, else Failed. See Note [Array kinds]
    IsElementOf(usize, usize), // Resumed with Matched if STACK[a] was loaded from STACK[b]'s array
                               // part, else Failed. See Note [Array kinds]
    ArrayType(usize, Root), // Inform the executor that STACK[a] was loaded from the array part
                            // of the table in a root (as `Subject` answered before the load): its
                            // type is the array's kind, if known. See Note [Array kinds]
    Subject(usize), // Resumed with Subject: the upvalue STACK[idx] holds the value of, if the
                    // context knows, else the slot. See Note [Upvalue paths]
    FieldType(usize, HashRef), // Inform the executor that STACK[idx]'s type is the same as an HREF's field.
                               // See Note [Field types]
    LoadGlobal(usize, usize), // STACK[idx] was just loaded with global CONSTANT[k]. See Note [Field facts]
    LoadUpvalue(usize, usize), // Infrom the executor that STACK[idx]'s type is the same as an UPVALUE[b].
                               // See Note [Fragile information]
    UpvalueKnown(usize), // Resumed with what the context knows of UPVALUE[idx]'s value: Boxed, the
                         // native it holds; else Integer, a stack slot holding it; else Failed.
                         // See Note [Fragile information]
    UpvalueCell(usize), // Resumed with UPVALUE[idx]'s cell, and whether it holds the value, as
                        // Cell; else Failed, if it has none. See Note [Upvalue cells]
    Captures(usize, Vec<(Opcode, usize)>), // Inform the executor that the closure in STACK[a]
                                           // captured these upvalues, as CLOSURE's pseudo-
                                           // instructions name them. See Note [Upvalue paths]
    Close(usize), // Inform the executor that the upvalues open into STACK[a] and up are closed.
                  // See Note [Upvalue paths]
    UpvalueHolds(usize, usize), // Inform the executor that UpValue[a] holds STACK[b]'s value. See
                                // Note [Upvalue paths]
    Copy(usize, usize), // Inform the executor that STACK[a] holds STACK[b]'s value. See Note
                        // [Value classes] in `classes`
    Effect(Effect), // An effect on fragile information the residuals yielded don't show. See
                    // Note [Fragile information]

    HashKey(usize, usize, bool), // Looks up or allocates an HREF for STACK[idx][key]; down its `__index` chain if true (a load). See Note [Table metatables]
    HashKeyNamed(usize, LConstant<'static, 'static>, bool), // `HashKey` of a key known by its value
    MemoryOp(crate::peephole::MemOp), // The table access the window yielded next is. See Note [Peephole memory]
    // What the peephole yields. See Note [Peephole fusion] in `peephole`.
    Holding { writes: Vec<usize>, reads: Vec<usize>, constant: Option<(usize, i32)>, optimistic: bool }, // An integer op held:
                                // writing `writes` from `reads`, folded to `constant` if it says
    Fused { op: Rc<dyn Window>, exit: Vec<Rc<dyn Window>>, unknown: Vec<usize> }, // What is held laid out, an op that
                                // can fail: its exit writes `exit`, leaving `unknown` unknown
    Took, // A guard the peephole joined to what it holds, as passed
    FrameUnmade, // Resumed with the closure the code's inlined call calls, Boxed, if its frame isn't
                 // made and the closure is known, else Failed. See Note [Peephole fusion]
    HoldsValue(usize, usize), // Resumed with Matched if STACK[dest] holds STACK[src]'s value
                              // already, a move between them nothing. See Note [Peephole fusion]
    Created(usize), // STACK[idx] holds a table just made, which nothing watches. See Note [Watched tables]
    LayOut, // Lay out everything held
    LaidOut(Rc<dyn Window>), // What the peephole held, laid out: the context knew what it does when it was held
    Continue(Pc), // The code goes on at pc straight on: resumed with Matched once the peephole is given
                  // its generator, else Failed. See Note [Peephole fusion]
    NextPc, // The instruction's generator is done: resumed with Matched once the peephole is given
            // the next's, else Failed. See Note [Peephole fusion]
    Enter, // Move the base to the frames of the inlined calls the code is in that it isn't in
    MakeFrames, // Make the frames of the inlined calls the code is in that aren't, the code going on inside them
    PeepholeTrace(&'static str, Vec<(&'static str, String)>), // A trace event of what the peephole did
    Watching(usize, bool), // A watch site of STACK[idx]'s table, frozen first if the bool says so:
                           // resumed with Matched, the code after knowing which table it is,
                           // while it is watched, else Failed. See Note [Watched tables]
    FrozenElement(usize, usize), // The element of STACK[table] at RK(key), if the table is frozen and the
                                 // key known: resumed with Element, else Failed. See Note [Frozen tables]
    Discovered(usize, u64, CType, Option<i32>), // STACK[idx] holds the element `Element` resumed with.
                                                // See Note [Frozen tables]
    ValueOf(usize), // STACK[idx]'s value, if known: resumed with Boxed, else Failed
    Uniques(Vec<usize>), // A slot of each class known unique but the slots', resumed with Slots, else
                         // Failed if one has none. See Note [Disjoint tables]
    Unique(Vec<usize>), // STACK[idx]'s values are known unique. See Note [Disjoint tables]
    Trip(Option<usize>), // A store into STACK[idx]'s table, or with none the environment, is about
                         // to be laid out: resumed with Matched. See Note [Watched tables]
    Learn(usize), // Resumed with Keys: the string keys of STACK[idx]'s table, once the code runs. See
                  // `jit.learn` in `library`
    LearnKind(usize), // Resumed with Matched once the context knows STACK[idx]'s table's array
                      // part's kind, found out at runtime, if it is of one; else Failed
    IsKey(usize, &'static [u8]), // Whether CONSTANT[k] is the string of these bytes: Matched, else Failed
    UpdateHashRef(HashRef, Option<LType>), // Update the type of HREF to a new type, if known
    GlobalCache(usize), // Resumed with a Cache for global CONSTANT[k]. See
                        // Note [Global caches]
    SetKeyHazards(usize), // SetHazards, for the hash keys of CONSTANT[k] only
    SetHazards(Option<usize>, Option<HashRef>), // Set optimization hazards, potentially
                                        // scoped to only information that may alias with an href,
                                        // and potentially keeping information about a specific
                                        // stack slot intact.
    CollectGarbage,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HashKey<'src, 'intern> {
    /// The slot of the table the key is in.
    pub idx: usize,
    pub key: LConstant<'src, 'intern>,
    /// Its field's type, `Mixed` if it isn't stable; `None` if the index is
    /// free. A shape or a function's identity describes a register, not a
    /// field, so a field's type is a representation. See Note [Field types].
    pub known_type: Option<Kind>,
    /// Per slot: whether access through that slot is already checked for
    /// aliasing, so it needs no epoch check.
    pub hazards: SmallVec<[bool; 8]>,
    /// Where the table its field is in comes from: `idx`'s register, or down
    /// that register's table's `__index` chain. See Note [Table metatables].
    pub place: Place,
    /// For a key its table lacks, or has nil, found down the table's `__index`
    /// chain: the hash key it's found at. See Note [Table metatables].
    pub chain: Option<HashRef>,
}

/// The slot a hash key of a frame an inlined callee is inlined into is in, as the callee sees it:
/// past any of its own. See Note [Inlined calls].
const OUTER: usize = usize::MAX;

/// How many `__index` hops down a table's chain a hash key's field can be.
/// See Note [Table metatables].
const MAX_CHAIN: usize = 3;

impl<'src, 'intern> HashKey<'src, 'intern> {
    fn tostring(&self, owner: &Owner) -> String {
        if self.orphan() {
            return "free".to_string();
        }
        let lv: LValue = (&self.key).into();
        // The slots accesses through which are checked, if any.
        let checked: Vec<String> = self.hazards.iter().enumerate().filter(|(_, checked)| **checked).map(|(slot, _)| slot.to_string()).collect();
        format!("hkey({}, {}{})",
            String::from_utf8_lossy(lv.as_string_nolock().unwrap().as_slice()).to_owned().replace("\0",""),
            self.known_type.map_or("free".to_string(), |t| t.to_string()),
            if checked.is_empty() { String::new() } else { format!(", checked {}", checked.join(" ")) })
    }

    /// A new hash key, its index reserved until its href thunk finds its type.
    fn new(idx: usize, key: LConstant<'src, 'intern>) -> Self {
        HashKey { idx, key, known_type: None, hazards: Default::default(), place: Place::Register, chain: None }
    }

    /// Whether access through slot `at` needs no epoch check.
    fn checked(&self, at: usize) -> bool {
        self.hazards.get(at) == Some(&true)
    }

    /// Record that access through slot `at` needs no epoch check.
    fn check(&mut self, at: usize) {
        if self.hazards.len() <= at {
            self.hazards.resize(at + 1, false);
        }
        self.hazards[at] = true;
    }

    /// Make every access check the epoch again.
    fn clear_checks(&mut self) {
        self.hazards.iter_mut().for_each(|checked| *checked = false);
    }

    /// Whether this index is free for a new hash key. See Note [Field types].
    fn orphan(&self) -> bool {
        self.known_type.is_none()
    }

    /// A free index, as every free index is: what the hash key there was tells nothing. See
    /// Note [Version compatibility].
    fn free() -> Self {
        HashKey { idx: OUTER, key: crate::chunk::Constant::Nil, known_type: None, hazards: SmallVec::new(), place: Place::Register, chain: None }
    }

    /// Whether blocks compiled knowing `self` are correct for a context with
    /// `other` at the same index. See Note [Version compatibility].
    fn accepts(&self, other: &Self) -> bool {
        self.idx == other.idx
            && self.key == other.key
            && self.place == other.place
            && self.chain == other.chain
            && match (self.known_type, other.known_type) {
                (Some(mine), Some(theirs)) => mine == theirs || mine == Kind::Mixed,
                (mine, theirs) => mine == theirs,
            }
            && self.hazards.iter().enumerate().all(|(slot, &checked)| !checked || other.hazards.get(slot) == Some(&true))
    }
}


/// How two cells are, as `ctx` knows their tables and keys. See Note [Peephole memory] in `peephole`.
fn cells(ctx: &Context, a: crate::peephole::Element, b: crate::peephole::Element) -> crate::peephole::Alias {
    use crate::peephole::{Alias, Operand};
    let same = |x: usize, y: usize| x == y || ctx.values.same(Loc::root(Root::Slot(x as u16)), Loc::root(Root::Slot(y as u16)));
    let constant = |key: Operand| match key {
        Operand::K(k) => Some(k),
        Operand::Slot(slot) => ctx.constant(slot),
    };
    // A table known watched is no held store's: a store into it trips first, in its instruction,
    // and goes on elsewhere, and the elements code knows of it stay what they were. See Note
    // [Watched tables].
    let watched = |table: usize| ctx.values.fact(Loc::root(Root::Slot(table as u16)), WATCHED).is_some();
    if watched(a.table) || watched(b.table) {
        return Alias::Disjoint;
    }
    // Two unique classes are two tables. See Note [Disjoint tables].
    let unique = |table: usize| ctx.values.fact(Loc::root(Root::Slot(table as u16)), UNIQUE).is_some();
    if unique(a.table) && unique(b.table) && !same(a.table, b.table) {
        return Alias::Disjoint;
    }
    // Different keys are different elements, whatever the tables.
    let keys = match (constant(a.key), constant(b.key), a.key, b.key) {
        (Some(x), Some(y), _, _) if x != y => return Alias::Disjoint,
        (Some(_), Some(_), _, _) => true,
        (_, _, Operand::Slot(x), Operand::Slot(y)) => same(x, y),
        _ => false,
    };
    if keys && same(a.table, b.table) { Alias::Same } else { Alias::May }
}

/// Where an exit of what the peephole holds goes on from: the start of an instruction, in its
/// context, or where compiling went on in one, nothing held: at a pc, in a context, with a
/// generator and what it resumes with. See Note [Peephole fusion] in `peephole`.
#[derive(Clone)]
enum Restart {
    Start(Rc<Context>),
    Resume(SubPc, Rc<Context>, Box<Gen>, ResumeArg),
}

impl Restart {
    /// It, the frames of its inlined calls as made as `now`'s: what is laid out moving the base or
    /// making them stays, so a restart from before goes on from there. See Note [Peephole fusion]
    /// in `peephole`.
    fn made_as(&mut self, now: &Context) {
        let (Restart::Start(ctx) | Restart::Resume(_, ctx, _, _)) = self;
        for (frame, now) in Rc::make_mut(ctx).inline.iter_mut().zip(&now.inline) {
            frame.made = now.made;
        }
    }
}

/// Where compiling an instruction went on to, if it went on in the block: the next instruction, in
/// what context, what its generator returned, and what the peephole holds still. See Note
/// [Peephole fusion] in `peephole`.
pub type Compiled = Option<(Pc, Rc<Context>, ResumeArg, crate::peephole::Spells)>;

/// Whether an integer op's result fits the integer encoding for the values its operands have.
/// See Note [Optimistic ops].
#[derive(Clone)]
pub struct Fits(pub Rc<dyn Fn(&RunState) -> bool>);

impl std::fmt::Debug for Fits {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("fits")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ResumeArg {
    Subject(Root),
    Start,
    Matched,
    MatchedConst(usize),
    Failed,
    Type(CType),
    BlockId(BlockId),
    HashRef(HashRef, Kind),
    Integer(i32),
    Number(f64),
    Boxed(u64),
    /// A frozen table's element: boxed, its type, and its value if an integer. See Note [Frozen
    /// tables].
    Element(u64, CType, Option<i32>),
    /// See Note [Global caches].
    Cache(*const GlobalCache),
    /// The end of a call's arguments, and the type its native's window op
    /// assumes they have.
    WindowArgs(usize, CType),
    /// An upvalue's cell, and whether it holds the upvalue's value. See Note [Upvalue cells].
    Cell(usize, bool),
    /// A table's string keys. See `jit.learn` in `library`.
    Keys(Rc<[LConstant<'static, 'static>]>),
    Slots(Rc<[usize]>),
}

// Initialize a hash key: `at` is `index << 8 | href`. Its hot path finds the table's entry at
// `index` has the key `key` and the frame's witness for `href` has its place, populating the
// witness; its cold path finds the key wherever it is (`href_init_slow`). Exit 0 if the table has
// the key, where the field's type is guarded (`GuardWitness`), and 1 if not. See Notes [Hash
// witnesses] and [Field types].
windowed!(fields HrefInit, [at: u64, key: u64], [], |owner, state, base| (table) {
    let (href, index) = (at as u8, (at >> 8) as usize);
    let hidx = state.witness_base + href as usize;
    let LValue::Table(tab) = table.unbox() else { unreachable!() };
    let address = tab.0.to_addr();
    let hit = {
        let tab = tab.rw(owner);
        let epoch = tab.epoch;
        match tab.hash.get_index_mut(index) {
            Some((k, value)) if k.boxed().bits() == key => Some((epoch, value as *mut LBoxed<'_, '_>)),
            _ => None,
        }
    };
    match hit {
        Some((epoch, value)) if hidx < state.hash_witnesses.len() => {
            state.witness_top = state.witness_top.max(hidx + 1);
            state.hash_witnesses[hidx] = HashWitness { epoch, index, value: value.cast(), table: address };
            false
        },
        _ => true,
    }
} cold {
    let (href, index) = (at as u8, (at >> 8) as usize);
    let LValue::Table(tab) = table.unbox() else { unreachable!() };
    href_init_slow(owner, state, tab, href, index, key)
});

// `HrefInit` for a hash key of a userdata, in its `__index` table: exit 0 if that has the key,
// populating the witness, and 1 if not, or if it has no `__index` table. See Note [Userdata
// fields].
windowed!(fields select HrefInitIndex, [at: u64, key: u64], [], |owner, state, base| (userdata) {
    let (href, index) = (at as u8, (at >> 8) as usize);
    let LValue::Userdata(u) = userdata.unbox() else { unreachable!() };
    match u.ro(owner).index_table(owner, &state.index_key) {
        Some(tab) => href_init_slow(owner, state, tab, href, index, key),
        None => 1,
    }
});

// `HrefInit` for a hash key at a place down its register's `__index` chain (`place`, as
// `Place::bits`): exit 0 if the table there has the key, populating the witness, and 1 if not,
// or if there's no table there. See Note [Table metatables].
windowed!(fields select HrefInitAt, [at: u64, key: u64, place: u16], [], |owner, state, base| () {
    let (href, index) = (at as u8, (at >> 8) as usize);
    match state.place_table(owner, 0, Place::from_bits(place)) {
        Some(tab) => href_init_slow(owner, state, tab, href, index, key),
        None => 1,
    }
});

/// `HrefInit`'s cold path: the key isn't at `index`, or the witness's place isn't there yet,
/// which it makes. Exit 0 if `tab` has the key, populating the witness, and 1 if not.
/// `rust-cold` (LLVM's `preserve_most`), so the cold stencil calling it with its window live
/// needn't save the window around the call.
extern "rust-cold" fn href_init_slow<'src, 'intern>(owner: &mut Owner, state: &mut RunState<'src, 'intern>, tab: Tc<Table<'src, 'intern>>, href: u8, index: usize, key: u64) -> usize {
    let hidx = state.witness_base + href as usize;
    state.hash_witnesses.grow(hidx + 1);
    state.witness_top = state.witness_top.max(hidx + 1);
    // Safety: the key is a constant's, which outlives the code using it.
    let key: LCanon<'src, 'intern> = unsafe { LCanon::from_bits(key) };
    let address = tab.0.to_addr();
    let found = match tab.ro(owner).hash.get_index(index) {
        Some((k, _)) if *k == key => Some(index),
        _ => tab.ro(owner).hash.get_index_of(&key),
    };
    let tab = tab.rw(owner);
    let epoch = tab.epoch;
    match found {
        Some(index) => {
            let value = tab.hash.get_index_mut(index).unwrap().1 as *mut LBoxed<'_, '_>;
            state.hash_witnesses[hidx] = HashWitness { epoch, index, value: value.cast(), table: address };
            0
        },
        None => {
            debug!("href_init missing key");
            state.hash_witnesses[hidx] = HashWitness { epoch, index, value: core::ptr::null_mut(), table: address };
            1
        },
    }
}

/// A global's cache: where its value is in the global environment, while the
/// environment's entries haven't moved since. See Note [Global caches].
pub struct GlobalCache {
    pub(crate) key: LCanon<'static, 'static>,
    /// `env_moves()` when `value` was found; `u64::MAX` before.
    moves: Cell<u64>,
    value: Cell<*mut LBoxed<'static, 'static>>,
}

impl GlobalCache {
    fn new(key: LCanon<'static, 'static>) -> Self {
        GlobalCache { key, moves: Cell::new(u64::MAX), value: Cell::new(core::ptr::null_mut()) }
    }

    /// The entry's address, if the cache holds it.
    pub(crate) fn hit(&self) -> Option<*mut LBoxed<'static, 'static>> {
        (self.moves.get() == crate::vm::env_moves()).then(|| self.value.get())
    }

    /// Look the key up again: its entry's address, or `None` if the environment
    /// lacks it.
    pub(crate) fn refill(&self, owner: &mut Owner, env: &Tc<Table<'_, '_>>) -> Option<*mut LBoxed<'static, 'static>> {
        let key: &LCanon<'_, '_> = unsafe { core::mem::transmute(&self.key) };
        let (_, _, value) = env.rw(owner).hash.get_full_mut(key)?;
        self.value.set((value as *mut LBoxed<'_, '_>).cast());
        self.moves.set(crate::vm::env_moves());
        Some(self.value.get())
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
pub(crate) use drain;

// Note [Captured slots]
// ~~~~~~~~~~~~~~~~~~~~~
// A closure's upvalue is a cell shared by every closure capturing the same variable. While the
// variable's frame runs, the cell is open, naming its stack slot. When the frame returns,
// `close_upvalues` closes it, moving the slot's value into it. A CLOSURE's pseudo-instructions say
// where each upvalue comes from: a MOVE a slot of the running frame, whose open cell the closure
// shares with any other captures, and a GETUPVAL the running closure's own upvalue.
//
// A closure may read or write a slot it captured whenever it runs, which is during a call. For
// that reason, the type of a slot any CLOSURE of a function captures (`captured_slots`) is
// forgotten after each call that isn't a pure native's (Note [Library natives] in `library`), and
// no context types a captured slot with what a call may have changed.
//
// GETUPVAL and SETUPVAL read and write an open cell's slot in memory, never the
// register window: it is a slot of an enclosing frame, below the running one's.

/// The slots of `proto`'s frame some CLOSURE in it captures. See Note [Captured
/// slots].
pub fn captured_slots<'src, C>(proto: &crate::chunk::FunctionBlock<'src, C>) -> Vec<usize> {
    let code = &proto.instructions.items;
    let mut captured = vec![];
    for (pc, inst) in code.iter().enumerate() {
        if inst.0.Opcode() == Opcode::CLOSURE {
            let (_, bx) = crate::vm::ABx::unpack(inst.0);
            let upvalues = proto.prototypes.items[bx as usize].upval_count as usize;
            for pseudo in &code[pc + 1..pc + 1 + upvalues] {
                if pseudo.0.Opcode() == Opcode::MOVE {
                    captured.push(crate::vm::AB::unpack(pseudo.0).1 as usize);
                }
            }
        }
    }
    captured.sort();
    captured.dedup();
    captured
}

/// The window op for `CALL A B C` in `ctx`, if STACK[A] is a native with fixed arity,
/// and it has enough arguments. The arguments may either be fixed, or the top the call
/// before left, if known (Note [Known top]). See Note [Native windows].
fn native_window(ctx: &Context, a: usize, b: usize, c: usize) -> Option<(usize, crate::vm::NativeOp)> {
    let CType::NativeFunction(nf) = &ctx.types[a] else { return None };
    native_op(ctx, nf, a, b, c)
}

/// `native_window`, for the native `nf` in R(A) however it is known.
fn native_op(ctx: &Context, nf: &NClosure, a: usize, b: usize, c: usize) -> Option<(usize, crate::vm::NativeOp)> {
    let end = if b == 0 { ctx.top? } else { a + b };
    let ints: SmallVec<[bool; 4]> = (a + 1..end).map(|slot| ctx.slot(slot) == CType::Type(LType::Integer)).collect();
    // A call taking every result gets the op's one.
    nf.window(a, (end - a) as u16, if c == 0 { 2 } else { c as u16 }, &ints).map(|op| (end, op))
}

// The frame's top, at `slot`: after a native's window op with C = 0. See Note
// [Known top].
windowed!(SetTop, [slot: usize], [], |owner, state, base| () {
    state.top = state.base + slot;
});

// Note [Returns]
// ~~~~~~~~~~~~~~
// A return is in two halves, each where one of its counts is known.
// The callee's (at its RETURN, which knows B) pops its frame and moves its results down to the
// slot the function was called from, with the top just past them.
// The caller's (in the `Arrive` residual right after the call, which knows C) pads them with nil
// to the count it wants, and shrinks the stack back to its frame (Note [Stack frames]).
//
// A lua call must return to the residual after it: its `Arrive`, or its continuation's guard, before
// an `Arrive` of its own (Note [Call continuations]). Its `Location` is that residual, so every way
// back into the caller takes its results there, whether the callee returns to the caller's JIT
// code, to the interpreter running the caller, or through a bailout.
// A native call *must not*; `call_native` puts the results in place by itself, and running
// `Arrive` additionally would be incorrect. For known native functions we may skip emitting the
// `Arrive` in the first place. However, for dynamic calls where it is not known until runtime if a
// callee is a lua or native function, it must dynamically perform a jump.

/// The id of a return whose results aren't known (B = 0). See Note [Call
/// continuations].
pub const UNKNOWN_RETURN: u32 = (1 << crate::vm::EFFECTS_SHIFT) - 1;

// Note [Call continuations]
// ~~~~~~~~~~~~~~~~~~~~~~~~~
// A call's continuation is specialized on what the callee returned (Chevalier-Boisvert & Feeley,
// "Interprocedural Type Specialization of JavaScript Programs Without Type Analysis"), by guarding
// on the return rather than on the types of the results. A `Ret`'s context at compile time says
// what it returns: the types of its results, and, with B, how many. Those are interned into an id,
// the same for every return of the same (`Specializer::returns`), or with B = 0, unknown
// (`UNKNOWN_RETURN`). A return leaves JIT code with `RETURNED | effects << EFFECTS_SHIFT | id`, its
// function's effects with the id (Note [Call effects]; the call's return value, where the call is
// in JIT code), and sets `RunState::returned` to the same, from JIT code or the interpreter.
//
// After a call to a Lua function (a `LuaCall`), the caller continues at a thunk, not an `Arrive`.
// Forced just after a return, it lays out a guard on that return (`ReturnedFrom`), comparing the
// call's return value (`returned` where the interpreter runs it, or where JIT code is entered at
// the guard), the thunk for the next return on its failure, and on its success an `Arrive` knowing
// the count (`Arrived`) and a jump to a version of the code after the call knowing the results'
// types (and with C = 0, the top), and what of the caller's context before the call the callee's
// effects keep. A return whose results aren't known (B = 0), or one past `MAX_VERSIONS`, continues
// as a call without: `Arrive` and the version knowing nothing of the results or of the callee's
// effects. That version is only found, and compiled, when a layout jumps to it (`After`): one
// made up front would take one of the pc's versions whether or not anything ever enters it, and
// once the pc has `MAX_VERSIONS`, accept the contexts its continuations reach it with, knowing
// nothing of them. A native call doesn't return this way, and never reaches such a guard.
//
// A call inside an instruction (a generic for's of its iterator) continues where the call left its
// generator: the code after it is the generator, suspended at the call, resumed in the context the
// return gives, as the code after any other call is a version of the next pc (`Rest`). Such a call
// is not inlined while its callee's returns can give the instruction contexts that differ only in
// what the callee learned on rarer paths (`INLINE_RESUMES`): it continues straight after its
// return.

/// A TAILCALL's site: the context it is laid out from, its pc, A and B,
/// whether its function closes upvalues and is vararg, and that function's
/// effects. See Note [Tail calls].
struct TailSite {
    calling: Rc<Context>,
    pc: Pc,
    a: usize,
    b: usize,
    closes: bool,
    vararg: bool,
    effects: *const Cell<Effects>,
}

/// Where a call continues when nothing specializes its continuation: a block,
/// or the version of a pc for a context, found (and compiled) only when a
/// layout jumps to it. See Note [Call continuations].
#[derive(Clone)]
enum After {
    Block(BlockId),
    Version(Pc, Rc<Context>),
}

impl After {
    fn block(&self, vm: &mut Specializer, owner: &mut Owner) -> BlockId {
        match self {
            After::Block(block) => *block,
            After::Version(pc, ctx) => vm.version(owner, *pc, ctx.clone()),
        }
    }
}

// Note [Tail calls]
// ~~~~~~~~~~~~~~~~~
// A TAILCALL of a Lua function replaces the running function's frame with the callee's
// (`RunState::tail_call`), which returns where the running one would have: the stack doesn't grow
// however many tail calls follow one another. Its call site is specialized as a call's (Note
// [Call sites]): each Lua function it finds, up to `MAX_VERSIONS`, behind an identity guard, and
// the callee's version for the context the arguments have. Nothing continues after it.
//
// The return the caller's continuation guards on is the callee's (Note [Call continuations]), so
// its effects must cover what the tail caller did too (Note [Call effects]): each tail call joins
// the tail caller's effects into the callee's prototype's, as it runs. The tail caller's may grow
// after the tail call is laid out, by a path compiled later, so it is joined each time.
//
// JIT code does the same (`TailFrame`), then leaves its own native frame and jumps to the callee's
// code, so the callee's return is to what called the tail caller's code: the native stack
// doesn't grow either.
//
// A native in tail position, or what the site doesn't specialize, is called, and its results
// returned, as a RETURN of every result after a CALL would; its effects are unknown.

// Note [Frame ops]
// ~~~~~~~~~~~~~~~~
// JIT code and the interpreter share one Lua call stack: `state.callstack`, and the running frame
// in `state`. Whenever the interpreter runs, the callstack must be exactly what it would have made
// itself.
//
// A call from JIT code to JIT code makes no entry: it only moves the running frame to the callee's
// (`push_frame` without `ENTRY`), and counts the frames JIT code has called past the callstack's
// (`jit_depth`). The caller keeps what the entry would hold (its closure, base, and hash
// witnesses' range) on the native stack, and puts it back when the callee returns (`leave`
// without `ENTRY`), which only moves the results down. Either way the frame itself is made and
// left by the same code. A return from a frame JIT code didn't
// call pops its entry, as the interpreter's does.
//
// The callstack is made whole only when control leaves JIT code from inside frames it called.
// Each call there unwinds the bailout through its own code: it writes the entry of the frame it
// called at that frame's depth past the callstack's length, from what it kept and its own return
// location, in room the first one makes for all of them, and leaves in turn. Once the outermost
// leaves, the run loop takes them into the callstack (`finish_unwinding`), in order.
//
// Only a frame JIT code didn't call can be a vararg function's: its entry records its function's
// slot (Note [Vararg frames] in `vm`). A call from JIT code that would make one, or reach the
// interpreter's call path, while frames JIT code called are running, goes to the interpreter
// instead, which makes the callstack whole first. The frames JIT code called stay rooted for the
// collector without entries: each one's closure is in its function's slot, in its caller's frame,
// and while any runs, the collector marks the whole stack (Note [Stack frames] in `vm`). So is the
// closure of each frame that called one, which its call keeps on the native stack, but for the
// run's outermost frame, which has no function's slot: the run's state keeps that one
// (`RunState::entry`).
//
// JIT code runs the interpreter's own frame maintenance functions, not a copy of the logic. Each
// one is ran as a window op, copied into the JIT code, which means that the size of each function
// is very size and branch prediction sensitive.

// Note [Count case analysis]
// Callstack maintenance operations (See Note [Frame ops]) have differing behavior based on the
// arity of both the number of arguments and the number of returned values accepted.
//
// In order to avoid useless branches inside the window ops, which are size sensitive and going to
// have constants in their holes, we can perform case analysis on the dynamic values; this allows
// us to lift the dynamic choice into a static const parameter, and each monomorphized version of
// the window can constant fold away the branches it would never perform under each case.
//
// `Count` encodes which of {0, 1, 2, many} each argument is a case of.

/// Which of 0, 1, 2, or more a frame op's A, B or C is (Note [Frame ops]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, core::marker::ConstParamTy)]
pub enum Count {
    Zero,
    One,
    Two,
    Many,
}

impl Count {
    pub fn of(value: u16) -> Count {
        match value {
            0 => Count::Zero,
            1 => Count::One,
            2 => Count::Two,
            _ => Count::Many,
        }
    }

    /// What an op's hole holds for `value`
    pub fn hold(value: u16) -> u16 {
        // Past 2, `value - 3`, which LLVM requires in order to properly take advantage of
        // `unreachable` annotations around what `Count::Many` means.
        value.saturating_sub(3)
    }

    /// The value, of this count, a hole holding `held` (`hold`) stands for: a hole of any width, as
    /// wide as one load of it is.
    pub fn lift(self, held: impl Into<u64>) -> usize {
        match self {
            Count::Zero => 0,
            Count::One => 1,
            Count::Two => 2,
            Count::Many => held.into() as usize + 3,
        }
    }
}

// `push_frame`, without the callstack's entry, for a call of R(A), with CALL's B (`a` and `b` as
// `Count::hold` holds them), of a callee whose frame size is `frame`, or 0 to read it from the
// callee: the JIT code's copy's own, which the JIT patches as it grows. Requires nilling the
// callee's frame if `FILLS`, or else the JIT code does. The callee isn't vararg. See Notes [Frame
// ops] and [Inlined calls].
windowed!(frames frame PushFrame, [a: u16, b: u16, frame: u64], [FILLS: bool, A: Count, B: Count], |owner, state, base| () {
    state.push_frame::<false>(owner, crate::vm::PackedLocation::from_bits(0), A.lift(a), B.lift(b), frame as usize, FILLS);
    debug_assert!(unsafe { (*state.clos.ro(owner).prototype).is_vararg } == 0, "PushFrame of a vararg function's frame");
});

// `tail_call` for a tail call of R(A). `ab` is its `a | b << 16` (as `Count::hold` holds them);
// `effects` and `callee` the addresses of the running function's effects and the callee's, which
// the first is joined into (Note [Tail calls]). Closing upvalues if `CLOSES`, from a vararg
// function if `VARARG`. See Note [Frame ops].
windowed!(frames frame TailFrame, [ab: u64, effects: u64, callee: u64], [CLOSES: bool, VARARG: bool, A: Count, B: Count], |owner, state, base| () {
    let (a, b) = (A.lift(ab as u16), B.lift((ab >> 16) as u16));
    unsafe { *(callee as *mut u16) |= *(effects as *const u16) };
    state.tail_call(owner, a, b, CLOSES, VARARG);
});

// A `Ret` of R(A) and B (`a` and `b` as `Count::hold` holds them), returning `returns`, the id of
// what it returns (Note [Call continuations]), with its function's effects, at the address
// `effects` (Note [Call effects]); `at` (a `PackedLocation`) is where it is. Closing upvalues if
// `CLOSES`, returning from a vararg function if `VARARG`. A return from a frame JIT code called
// is the op; one from a frame with an entry, or the outermost, its cold path. See Note [Frame ops].
windowed!(frames frame PopFrame, [a: u16, b: u16, returns: u32, effects: u64, at: u64], [CLOSES: bool, VARARG: bool, A: Count, B: Count], |owner, state, base| () {
    state.returned_at = at;
    if state.jit_depth > 0 {
        let _ = state.leave::<false>(owner, A.lift(a), B.lift(b), CLOSES, VARARG);
        // See Note [Call continuations].
        state.returned = crate::vm::RETURNED | (unsafe { *(effects as *const u16) } as u64) << crate::vm::EFFECTS_SHIFT | returns as u64;
        state.exit = state.returned;
        false
    } else {
        true
    }
} rejoin {
    state.exit = if state.callstack.is_empty() {
        let Location(BlockId(block), off) = Location::unpack(crate::vm::PackedLocation::from_bits(at as usize));
        state.current_off = off as u16;
        ((-2i32 as u64) << 32) | block as u64
    } else {
        match state.leave::<true>(owner, A.lift(a), B.lift(b), CLOSES, VARARG) {
            // See Note [Call continuations].
            Ok(Some(location)) => {
                state.resume = location.pack().bits() as u64;
                state.returned = crate::vm::RETURNED | (unsafe { *(effects as *const u16) } as u64) << crate::vm::EFFECTS_SHIFT | returns as u64;
                state.returned
            },
            // With a caller frame's entry, `leave` returns to it.
            Ok(None) | Err(_) => unreachable!(),
        }
    };
});

// `shift_frame` without the callstack's entry, for an inlined call of `callee`, R(A), with CALL's B
// (`a` and `b` as `Count::hold` holds them), of a callee whose `max_stack` is `stack`, keeping the
// window: the JIT code nils the callee's frame. See Notes [Inlined calls] and [Count case
// analysis].
windowed!(frames ShiftFrame, [a: u64, b: u64, stack: u8], [A: Count, B: Count], |owner, state, base| (callee) {
    state.shift_frame::<false>(owner, callee, A.lift(a), B.lift(b), stack, false, 0);
});

// `ShiftFrame` as a frame op, nilling the callee's frame past its arguments, as many as there are
// or up to the top. See Notes [Inlined calls] and [Count case analysis].
windowed!(frames frame ShiftFrameFilled, [a: u16, b: u16, stack: u8], [A: Count, B: Count], |owner, state, base| () {
    let callee = state.vals[state.base + A.lift(a)];
    state.shift_frame::<false>(owner, callee, A.lift(a), B.lift(b), stack, true, 0);
});

// `unshift_frame` without the callstack's entry, for an inlined callee's RETURN A B (`a` and `b`
// as `Count::hold` holds them), closing its frame's open upvalues if `CLOSES`, moving its results
// if `MOVES`. See Notes [Inlined calls] and [Count case analysis].
windowed!(frames frame UnshiftFrame, [a: u16, b: u16], [CLOSES: bool, MOVES: bool, A: Count, B: Count], |owner, state, base| () {
    state.unshift_frame::<false>(owner, MOVES.then(|| (A.lift(a), B.lift(b))), CLOSES);
});

// Whether a table's array part has kind `kind`, testing an element loaded from it in place of
// the element's own tag. See Note [Array kinds].
windowed!(properties guard KindIs, [kind: LType], [], |owner, state, base| (table) {
    let LValue::Table(tab) = table.unbox() else { unreachable!() };
    tab.ro(owner).kind == kind.bit()
});
// The same of the table in the running closure's upvalue `index`.
windowed!(upvalues guard UpvalKindIs, [index: usize, kind: LType], [], |owner, state, base| () {
    let LValue::Table(tab) = state.upvalue(owner, index).unbox() else { unreachable!() };
    tab.ro(owner).kind == kind.bit()
});

// `arrive` for the call of R(A) before it. `ac` is its `a | c << 16` (as `Count::hold` holds
// them).
// See Note [Frame ops].
windowed!(frame Arrive, [ac: u64], [A: Count, C: Count], |owner, state, base| () {
    state.arrive(A.lift(ac as u16), C.lift((ac >> 16) as u16));
});

// Note [Subblocks]
// ~~~~~~~~~~~~~~~~
// A block is a version of the code at a `SubPc`, for a specialized context (Note [Version
// compatibility]). A `SubPc` is a Lua bytecode PC plus the answers to the questions the
// instruction's generator has asked so far, so a block can start partway through an instructions:
// when a question can only be answered at runtime, the block ends in a thunk, and forcing it
// compiles the rest of the generator from taht answer on in a new block (`subblock`).
//
// An answer steps the `SubPc` the same way whether the specializer answers it immediately or a
// thunk finds it out at runtime (`navigate`). This means that either case result in the same
// `SubPc` and context, and they can both reuse an existing block from the other if it already
// was emitted. This allows for generators that begin in two disparate contexts but that reach
// the same context after some series of effects can be merged instead of proliferating versions.
//
// However, this means that a generator must be able to be uniquely identified solely by its
// `SubPc` and the context it currently has:
// - Every compilation of an instructions must ask the same questions in the same order. Where one
// tests something at runtime and another already knows the answer, or doesn't need it, the other
// yields `Decided` in order to transition the `SubPc` in an equivalent way.
// - What a generator yields next must only be determined by its `SubPc` and context. A type it
// read earlier may since have been narrowed by later answers, or it may have deduplicated across a
// guard and none of the later operations may depend on information from a potentially different
// starting point.

pub type Pc = usize;
/// Where in an instruction a generator is: see Note [Subblocks].
#[derive(PartialEq, Eq, Clone, Copy, Hash, Debug)]
pub struct SubPc(usize, u128);

impl SubPc {
    pub fn new(pc: Pc) -> Self {
        SubPc(pc, 1)
    }
    fn next_pc(&self) -> Self {
        Self::new(self.0 + 1)
    }
    fn next_true(&self) -> Self {
        assert!(self.1 < (1 << 126));
        Self(self.0, (self.1 << 1) | 1)
    }
    fn next_false(&self) -> Self {
        assert!(self.1 < (1 << 126));
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
    /// Whether `STACK[idx]`, known to be of type `known`, has the type
    /// `expected`: either its type is `expected` or below it.
    /// Whether STACK[idx]'s representation is `expected`.
    Guard { idx: usize, expected: LType },
    /// Whether STACK[idx], a number, is in the encoding `expected` (`Integer` or
    /// `Double`).
    NumericGuard { idx: usize, expected: LType },
    Exec(ResidualExec),
    /// A copy&patch window op (see `crate::window`) to execute.
    ExecWindow(Rc<dyn Window>),
    /// A guard whose test is a window op: it selects 1 if passed, or 0 if failed. See Note
    /// [Dynamic guards].
    GuardDynamic(Rc<dyn Window>),
    Call { a: u16, b: u16, c: u16 },
    Select(Vec<(&'static str, BlockId)>),
    /// The way on after an optimistic op, as the op selects: 0 to `hot`, 1 to `cold`. JIT code
    /// takes it with no `select`: the op's cold path continues at `cold` itself. See Note
    /// [Optimistic ops].
    Branch { hot: BlockId, cold: BlockId },
    Jump(BlockId),
    /// A jump whose JIT code can be unlinked again, to exit to the interpreter here: a forced
    /// watch site, which a trip unpublishes. See Note [Watched tables].
    PatchableJump(BlockId),
    Thunk(ThunkRef),
    /// A store into STACK[idx]'s table, or with none the environment's, which is watched, trips its
    /// watchpoint: the run loop handles it, then goes on after it. See Note [Watched tables].
    Tripped(Option<usize>),
    /// A RETURN of `b - 1` values from R(A), or up to the top. Closes the frame's open upvalues.
    /// Functions which statically know they have no open upvalues may set `close = false` as an
    /// optimization. Then, whether the function is vararg (Note [Vararg frames]), the id of what
    /// it returns, or `UNKNOWN_RETURN` (Note [Call continuations]), and last its function's
    /// effects, which it returns with the id (Note [Call effects]).
    Ret(Pc, u8, u16, bool, bool, u32, *const Cell<Effects>),
    /// Whether the witness `href`'s index in the table in `tab` still holds its
    /// key, `key` (canonical bits), with a value of type `expected`.
    HashGuard { tab: usize, href: HashRef, key: u64, expected: LType },
    /// Whether hash key `href`'s field, read through its witness, has type
    /// `expected`: a `Guard` on the field rather than a slot. See Note [Field
    /// types].
    GuardWitness { href: HashRef, expected: LType },
    /// `place` its hash key's. See Note [Table metatables].
    EpochCheck { tab: usize, href: HashRef, place: Place },
    NativeGuard { idx: usize, ptr: *const () },
    NativeCall { nf: NativeFunc, a: u16, b: u16, c: u16 },
    /// A call to the Lua function in R(A), The target `entry` is a prototype a `LuaGuard` or the
    /// context knows, `callee`, whose `max_stack` is `stack`. `vararg` if the prototype is vararg
    /// (Note [Vararg frames]). See Note [Call sites].
    LuaCall { entry: CallEntry, a: u16, b: u16, c: u16, stack: u8, vararg: bool, callee: LProto<'static, 'static> },
    /// A tail call of the Lua function in R(A), `entry` as a `LuaCall`'s: its frame replaces the
    /// running function's, which closes its open upvalues if `closes` (as `Ret`) and is vararg if
    /// `vararg`. The running function's `effects` are joined into the callee's
    /// (`callee_effects`) first. See Note [Tail calls].
    TailCall { entry: CallEntry, a: u16, b: u16, closes: bool, vararg: bool, effects: *const Cell<Effects>, callee_effects: *const Cell<Effects> },
    /// The results of the call of R(A) before it, which returns here: `c - 1`
    /// of them, or with C = 0 all. See Note [Returns].
    Arrive { a: u16, c: u16 },
    /// A call's continuation guard: whether the call's return returned what the
    /// id names, with the effects, as `RETURNED | effects << EFFECTS_SHIFT |
    /// id`. See Notes [Call continuations] and [Call effects].
    ReturnedFrom(u64),
    /// `Arrive`, for a return of `returned` results. See Note [Call
    /// continuations].
    Arrived { a: u16, c: u16, returned: u16 },
    LuaGuard { idx: usize, ptr: *const () },
    /// The frame of an inlined call of R(A) with B, of a callee whose `max_stack` is `stack`: the
    /// callee's upvalue cells its entry knows hold their values (Note [Upvalue cells]), and whose
    /// returns continue compiling `continuation`. See Note [Inlined calls].
    Inline { a: u16, b: u16, stack: u8, cells: u32, continuation: *const Continuation },
    /// An inlined callee's RETURN A B, which closes its frame's open upvalues if `closes`: its
    /// results to the call's R(A), `call`, if `moves`, and the caller's frame back. See Note
    /// [Inlined calls].
    InlineReturn { a: u16, b: u16, closes: bool, call: u16, moves: bool },
    /// The base moved on `by` slots to an inlined call's frame, which isn't made: its code naming
    /// only slots runs there. See Note [Peephole fusion] in `peephole`.
    Enter(u16),
    /// The base moved back `by` slots from the frame `Enter` moved it to.
    Leave(u16),
    GC,
}

/// Where a `LuaCall` enters its callee. See Note [Call sites].
#[derive(Debug, Clone)]
pub enum CallEntry {
    /// Not found yet: the callee's version for this context, found when the
    /// call first runs.
    Context(Rc<Context>),
    /// The callee's version.
    Block(BlockId),
}

// Note [Call sites]
// ~~~~~~~~~~~~~~~~~
// A call site is specialized on the function it calls. Each new function it finds is guarded for
// and called directly, and a function that fails every existing guard is found out like any other
// type; past `MAX_VERSIONS` functions, the site makes a generic call. A site whose context knows
// its callee needs no guard.
//
// A Lua call is laid out in a version of its own point for the context at the call, which every
// path reaching it in that context jumps to, as paths rejoin after a guard: they share the one
// call, its continuation, and a callee inlined for it (Note [Inlined calls]).
//
// The callee is entered in a version specialized to what the caller knows of the arguments: the
// parameters have the arguments' types, and the unpassed ones are nil. Facts that the caller knows
// of its own frame (hash keys, fragile facts, etc) says nothing of the callee's, and are not
// passed along. A call whose argument count isn't known, or to a vararg function, enters the
// generic version.
//
// The callee's version is chosen when the call first runs, not while specializing the caller,
// which would compile callees of calls that never run and attempt to resolve a recursive call
// target too early. Any version accepting the entry context will do, so the call itself needs no
// further guard. JIT code calls that version's code directly, once it has some. See Note [Call
// linking] for how JIT code reaches it.

// Note [Inlined calls]
// ~~~~~~~~~~~~~~~~~~~~
// A call of a small Lua function can compile the callee's code into its caller's. The call's
// continuation, forced once the call has returned, decides to: from then on the call site jumps to
// the callee's code in place of its call. That code is compiled from the context the caller had at
// the call, renumbered from the callee's frame's base, and names the call, by where it is in its
// caller's code, so it is the callee's code for that call alone. What the code after the call is
// compiled from, the caller's context before the call and how it continues, is kept in the inlined
// call's entry in the callstack (`Continuation`). Each of the callee's returns ends in a thunk which,
// run, continues compiling the caller's code after the call from that context, with the results'
// types, less what the callee's code may have falsified (its effects, applied as a continuation
// applies a callee's; Note [Call effects]), with no guard on the return between, and becomes the
// return and a jump to that code; but where the callee's frame isn't made, none of its code
// observing it, the caller's code is compiled on from the return itself, the base moved back if
// it was, the results the peephole holds held and the rest moved (Note [Peephole fusion] in
// `peephole`). What the callee learns of a value it was
// passed, as a table's array kind, the caller's places holding it know on the return: the value
// of each argument is a place of the callee's code (`Root::Arg`) that none of it writes.
//
// The call making a generic for's iterator (`for k, v in f(t) do`) inlines from its first layout,
// before it has run: the loop is compiled from what the code after it knows, and a function whose
// loop runs once (its only call making the iterator) has no later call to learn from. Inlined, the
// iterator's closure comes back knowing its upvalues (Note [Upvalue paths]), and so does its own
// code inlined into the loop.
//
// A function's frames hold the frames of the calls inlined into it, to any depth: its frame size
// grows with each call inlined, so every frame of it a call makes, and the collector's live
// extent, has room for them, and making an inlined callee's frame never lengthens the stack. As it
// grows the stack is lengthened under its frames already running, and JIT code's calls of the
// function, which hold its size, are patched to the new one.
//
// The decision is kept with the callee's entry context, by the call's point and the callee. Code
// after an inlined call is compiled anew whenever the callee's return gives the caller a context
// of its own, laying out the calls after it again; a call laid out at a decided point, whose
// callee's entry context the decided one accepts, inlines from the first, with no call made
// first. A call whose entry the decided ones don't accept, as one specialized to other types, is
// decided again by its own continuation.
//
// At runtime the callee's frame is made and left as a call's (`Inline`, `InlineReturn`). In the
// interpreter its entry in the callstack returns to the code inlining it (`Return::Inlined`), not
// to a residual: to the interpreter, the collector and unwinding it is a frame as any other. JIT
// code makes no entry for it, as for a frame JIT code calls (Note [Frame ops]): it keeps what the
// entry would hold on the native stack and counts the frame (`jit_depth`), and code leaving JIT
// code from inside it writes the entry as a call's bailout does. The JIT knows how many inlined
// calls deep each block's code is as it compiles it, so each way out of JIT code unwinds as many:
// a region's exits per depth, and an exit through a snapshot by the depth the snapshot records.
// Entered from the interpreter inside inlined calls, JIT code takes their entries onto the native
// stack first (`RunState::adopt_inlined`).
//
// The callee's hash keys are the caller's (Note [Hash witnesses] in `vm`): its frame has its
// caller's witnesses, and its entry context the caller's hash keys at their indexes, an argument's
// its parameter's, with its shape, and every other's the caller's own, which the callee's code
// keeps, naming no slot of it (`OUTER`). So the callee's code finds a field of a table it was
// passed as its caller's code would, and does to the caller's hash keys what its caller's code
// would. Each of its returns gives the caller the hash keys it leaves: the caller's own it kept,
// and the rest free.
//
// The callee's code is its versions for the inlined call, which their contexts carry
// (`InlineFrame`), apart from its versions for its calls and for other inlined calls. Calls in
// inlined code inline in turn, to `MAX_INLINE_DEPTH` deep. A callee with a tail call or VARARG
// never inlines; `LUNACY_NO_INLINE` turns inlining off, to compare.
//
// Whether a call inlines is measured on the callee's code as the call ran it, not its bytecode:
// the continuation runs just after the return, which says where it was (`RunState::returned_at`),
// so the code an inlined call would run is likely the callee's code from the version the call
// entered that reaches that exit, back from it, as far as it is compiled, with the calls inlined
// into it: one exit's, not every version's of the callee returning the same types. Code that loops there doesn't inline. Its cost is its
// residuals that do work, less a credit for each guard the caller's facts can stand for once the
// callee runs in the caller's context: a guard of a value loaded from an upvalue (Note [Upvalue
// paths]), and a hash key's guard. A call inlines if what is left is within `MAX_INLINE_COST`.

/// A field's or a global's name, hashed: what a store with a key of that name may change. See
/// Note [Field facts].
fn name_hash(name: &[u8]) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = rustc_hash::FxHasher::default();
    name.hash(&mut hasher);
    hasher.finish()
}

// Note [Watched tables]
// ~~~~~~~~~~~~~~~~~~~~~~
// Code can know a table is watched, and its contents, as a constant element: every store
// into a table first checks whether it is (`Trip`), and one that is trips its watchpoint before it
// stores, so nothing runs past the store relying on what it changes. The knowledge enters the code
// only past a watch site, a thunk whose jump leads to the code knowing it, and is lost across code
// the specializer doesn't see (`Effect::Opaque`), as a native's store trips no frame's; a trip unpublishes each
// of the table's sites, the jump undone back into its thunk, which, forced again, compiles the code
// after it knowing nothing of the table. The store goes on knowing nothing through a watch, and so
// does each frame paused at a call: a trip leaves JIT code, which writes every frame's callstack
// entry, and each entry whose code after the call knows something through one is redirected to a fresh
// continuation compiled without it, which, for a context that knew none, is the code it had.
// Values already loaded from the table are what they were: facts follow values, so only what is
// known of the table's contents goes. A trip is an effect, and what was learned through a watch is
// whatever doesn't survive it: a domain learned that way says so, as any domain does of the
// effects it survives (Note [Fragile information]).
//
// A store's check passed, or the table just made, the code after it knows the table unwatched, and
// checks it no more until a watch may have made it watched. A watch is an effect too, which no table's being unwatched
// survives, so a callee's reaches its caller as its other effects do (Note [Call effects]).

// Note [Frozen tables]
// ~~~~~~~~~~~~~~~~~~~~~
// A table can be frozen (`jit.frozen`): watched, and code past its watch site knows which table it
// is. A load from it at a key the context knows reads the element as it compiles, and goes on with
// the value in its register, known: its type, constant, and boxed value. What the load knows of its
// register stays true after a trip, as facts follow values; that the table still holds it is known
// only through the watch, so code relying on it is unpublished by a trip as the watch's is. The
// table is kept alive until it trips, and a load reads it only until then; nothing reads a value
// back from what is known of it.

// Note [Disjoint tables]
// ~~~~~~~~~~~~~~~~~~~~~~~
// A class can be known unique (`jit.disjoint`): its value is no other unique class's, so elements
// of tables in two unique classes are different elements. A disjoint site checks its arguments
// are different tables, from each other and from a value of each class already unique, as a value
// may reach an argument through a name the context doesn't connect to it; a unique class no slot
// holds makes the site learn nothing. Classes otherwise say only which values are equal: a join
// keeps a class unique only if no other unique class is of its class on either side, and a
// context is accepted only if its classes for two unique ones are two.

/// Where a Lua call's returns go on, and how the code after it is compiled: as
/// `make_continuation_thunk` takes it. See Note [Watched tables].
#[derive(Clone)]
struct ContinuationSite {
    ctx: Rc<Context>,
    captured: Rc<[usize]>,
    rest: Rest,
    a: usize,
    c: usize,
    after: After,
}

/// A watch site of a table: the thunk at `at`, whose jump leads to code knowing its contents,
/// and the thunk to put back there, which compiles it knowing none. See Note [Watched tables].
struct WatchSite {
    at: Location,
    unwatched: ThunkRef,
}

// Whether a table, or the environment, is watched: its cold path trips its watchpoint. See Note
// [Watched tables].
windowed!(reads TripCheck, [], [], |owner, state, base| (table) {
    let LValue::Table(tab) = table.unbox() else { unreachable!() };
    if tab.ro(owner).watched {
        core::intrinsics::cold_path();
        true
    } else {
        false
    }
} cold {
    1
});
windowed!(reads TripCheckGlobal, [], [], |owner, state, base| () {
    if state._G.ro(owner).watched {
        core::intrinsics::cold_path();
        true
    } else {
        false
    }
} cold {
    1
});

/// An inlined call, for its callee's code: where its call is in its caller's code, the caller's
/// prototype, the call's A, what the callee's code may have done to the caller so far, and for
/// each parameter passed a table the caller holds below the call, the caller's slot holding it.
/// See Note [Inlined calls].
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct InlineFrame {
    pub call: Location,
    pub proto: LProto<'static, 'static>,
    pub a: u16,
    pub effects: Effects,
    pub passed: SmallVec<[(u16, u16); 2]>,
    /// How much of the frame code past here has made. See Note [Peephole fusion] in `peephole`.
    pub made: Made,
    /// The call's B, the callee's parameters and frame size, its cells, and its returns'
    /// continuation: what makes the frame.
    pub b: u16,
    pub params: u8,
    pub stack: u8,
    /// The closure it calls, boxed, if the caller knows which.
    pub closure: Option<u64>,
    pub cells: u32,
    pub continuation: *const Continuation,
}

/// How much of an inlined call's frame is made: none, the base moved to it (`Enter`), or all of it,
/// its callstack entry and closure too (`Inline`). See Note [Peephole fusion] in `peephole`.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Made {
    No,
    Base,
    Yes,
}

impl InlineFrame {
    /// The residual making the frame from its caller's: nilling it past its arguments, unless code
    /// in it ran already, which nilled its parameters past them (`Enter`).
    fn push(&self) -> Residual {
        let b = if self.made == Made::Base { self.stack as u16 + 1 } else { self.b };
        Residual::Inline { a: self.a, b, stack: self.stack, cells: self.cells, continuation: self.continuation }
    }

    /// The slots `Enter` moves the base on by to it.
    fn by(&self) -> usize {
        self.a as usize + 1
    }

    /// The caller's slot holding the table parameter `param` was passed, if it still holds it in
    /// `ctx`: a write to it forgets the shape it entered with.
    fn owner(&self, ctx: &Context, param: usize) -> Option<usize> {
        let (_, owner) = self.passed.iter().find(|&&(p, _)| p as usize == param)?;
        matches!(ctx.slot(param), CType::Shape(..)).then_some(*owner as usize)
    }
}

/// The code after an inlined call, which its callee's returns continue compiling: the caller's
/// prototype and context before the call, its captured slots below the call, the call's A and C,
/// a root of the caller's still holding the callee's closure (Note [Upvalue paths]), and how the
/// code after the call is compiled. Kept for as long as the specializer is, in the inlined call's entry in the
/// callstack by its address. See Note [Inlined calls].
#[derive(Clone)]
pub struct Continuation {
    proto: LProto<'static, 'static>,
    caller: Context,
    captured: Rc<[usize]>,
    a: u16,
    c: u16,
    closure: Option<Root>,
    /// The places below the call holding each argument's value, by the argument.
    args: Vec<(u8, Root)>,
    rest: Rest,
}

/// How the code after a call is compiled, from the context its return gives: the next pc's
/// version, or for a call inside its instruction, the generator suspended at the call, resumed.
/// See Note [Call continuations].
#[derive(Clone)]
pub enum Rest {
    Next(Pc),
    Resume(SubPc, Rc<dyn Fn(&mut Specializer, &mut Owner, Rc<Context>) -> BlockId>),
}

impl Rest {
    fn block(&self, vm: &mut Specializer, owner: &mut Owner, ctx: Rc<Context>) -> BlockId {
        match self {
            Rest::Next(pc) => vm.version(owner, *pc, ctx),
            Rest::Resume(_, resume) => resume(vm, owner, ctx),
        }
    }

    /// The pc the code after the call is at, for traces.
    #[cfg(feature = "tracing")]
    fn pc(&self) -> Pc {
        match self {
            Rest::Next(pc) => *pc,
            Rest::Resume(at, _) => at.0,
        }
    }
}

/// A Lua call laid out, which its continuation may inline: the block and offset of its `LuaCall`,
/// its point, the callee's prototype, the context at the call and its B, and the peephole as it
/// was at the call, where what it held is laid out (`start`), which the call inlined goes on from,
/// and the call's restart. See Notes [Inlined calls] and [Peephole fusion] in `peephole`.
struct InlineCall {
    block: BlockId,
    off: usize,
    pc: SubPc,
    callee: LProto<'static, 'static>,
    calling: Rc<Context>,
    b: usize,
    coro: Box<Gen>,
    start: Location,
    restart: Option<(Pc, Restart, bool)>,
}

/// How many inlined calls deep code can be. See Note [Inlined calls].
pub(crate) const MAX_INLINE_DEPTH: u8 = 2;
/// Whether a call inside an instruction is inlined. See Note [Call continuations].
const INLINE_RESUMES: bool = true;
/// The most an inlined callee's code costs, less its credit. See Note [Inlined calls].
const MAX_INLINE_COST: usize = 48;
/// The credit for each guard of an inlined callee's code the caller's facts can stand for. See Note
/// [Inlined calls].
const REUSED_GUARD_CREDIT: usize = 4;
/// The upvalues of each frame, from the first, that have a cell. See Note [Upvalue cells].
pub const UPVALUE_CELLS: usize = 8;
/// The upvalue cells of a JIT code's activation: its own frame's and each inlined call's.
pub const CELLS: usize = UPVALUE_CELLS * (MAX_INLINE_DEPTH as usize + 1);
const _: () = assert!(CELLS <= u32::BITS as usize);

/// Whether calls inline: unless `LUNACY_NO_INLINE` is set, to compare. See Note [Inlined calls].
fn inlining() -> bool {
    static INLINES: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var_os("LUNACY_NO_INLINE").is_none());
    *INLINES
}

/// How many slots past the base of the outermost frame inlining it the frame of code of `ctx` is.
/// See Note [Inlined calls].
fn inline_offset(ctx: &Context) -> usize {
    ctx.inline.iter().map(|frame| frame.a as usize + 1).sum()
}

/// The slots past the base of the outermost frame an inlined callee's frame may reach: the JIT's
/// window names them (`Slots`). See Note [Inlined calls].
const MAX_INLINE_SLOTS: usize = 256;

/// Whether the call at `pc` in `proto`, of R(A), makes a generic for's iterator: a JMP to a
/// TFORLOOP of the same A follows it. See Note [Inlined calls].
fn makes_iterator<C>(proto: &crate::chunk::FunctionBlock<'_, C>, pc: Pc, a: usize) -> bool {
    let instructions = &proto.instructions.items;
    let Some(jmp) = instructions.get(pc + 1).filter(|inst| inst.0.Opcode() == Opcode::JMP) else { return false };
    let target = ((pc + 2) as isize + crate::vm::sBx::unpack(jmp.0) as isize) as usize;
    instructions.get(target).is_some_and(|inst| inst.0.Opcode() == Opcode::TFORLOOP && crate::vm::ABC::unpack(inst.0).0 as usize == a)
}

/// The lowest slot `ctx` knows holds the value slot `slot` does, of those `ok` takes: a name for
/// what a held store names `slot` by. See Note [Peephole memory] in `peephole`.
fn same_value(ctx: &Context, slot: usize, ok: impl Fn(usize) -> bool) -> Option<usize> {
    ctx.values.members(Loc::root(Root::Slot(slot as u16))).into_iter()
        .filter_map(|root| match root { Root::Slot(s) => Some(s as usize), _ => None })
        .filter(|&s| s != slot && ok(s))
        .min()
}

/// `held`'s stores naming no slot `dead` says is, in `ctx`, where another slot holds the value: a
/// held store is of a value, whichever slot names it. See Note [Peephole memory] in `peephole`.
fn rehome(held: &mut crate::peephole::Spells, ctx: &Context, dead: impl Fn(usize) -> bool) {
    let written: Vec<usize> = held.spells.iter().map(|spell| spell.dest).collect();
    held.rehome(|slot| dead(slot).then(|| same_value(ctx, slot, |s| !dead(s) && !written.contains(&s))).flatten());
}

/// What the peephole holds, `held`, at a call of R(A) with B of `callee` that is inlined: what's laid
/// out first, as the callee's code names none of it, and what goes on held into the callee's code,
/// in its slots. What names the caller's slots below the callee's frame is laid out; what writes the
/// frame past its arguments is dead, as entering it leaves those slots unset, nil to its code, and
/// what reads them reads them as they were. One passed what's up to the top, or whose code is its
/// return, takes nothing. See Note [Peephole fusion] in `peephole`.
fn entering(held: &crate::peephole::Spells, calling: &Context, callee: LProto<'static, 'static>, a: usize, b: usize) -> (crate::peephole::Spells, crate::peephole::Spells) {
    let stack = unsafe { (*callee).max_stack } as usize;
    // A store named by a slot below the frame is named by an argument holding the same value.
    let mut held = held.clone();
    if b != 0 {
        rehome(&mut held, calling, |slot| !(a + 1..a + b).contains(&slot));
    }
    // Code that is its return holds nothing to go on with.
    let returns = unsafe { (&(*callee).instructions.items)[0].0.Opcode() } == Opcode::RETURN;
    let (below, nilled): (Vec<usize>, Vec<usize>) = match b {
        _ if returns => ((0..a + 1 + stack).collect(), Vec::new()),
        0 => ((0..a + 1 + stack).collect(), Vec::new()),
        b => ((0..=a).collect(), (a + b..a + 1 + stack).collect()),
    };
    // What reads the frame's slots past the arguments reads them as they were: entering it writes
    // none of them, holding them unset.
    let (laid, kept) = held.split(&crate::peephole::Need { reads: below.clone(), writes: below, memory: false });
    let mut kept = kept.renamed(|slot| slot - a - 1, |slot| slot - a - 1, |slot| !nilled.contains(&slot), usize::MAX);
    // Its frame is nil past its arguments, as the peephole holds it, unset.
    if b != 0 {
        let fresh: Vec<usize> = (b - 1..stack).filter(|slot| !kept.unset.contains(slot)).collect();
        kept.unset.extend(fresh);
    }
    (laid, kept)
}

/// For a Lua callee's continuation, which applies only what the callee's effects falsify: the
/// context `ctx` before the call of R(A), but for the callee's frame, from `a` on, and the slots
/// below it closures capture of `captured`. See Note [Call effects].
fn before_call(owner: &mut Owner, ctx: &Context, captured: &[usize], a: usize) -> (Rc<Context>, Rc<[usize]>) {
    let mut before = ctx.clone();
    for idx in a..before.types.len() {
        before.effect(Effect::Write(idx));
    }
    let frame = (a..before.types.len()).map(|idx| (idx, CType::Unknown)).collect();
    before.set_types(owner, frame);
    let captured: Rc<[usize]> = captured.iter().copied().filter(|&slot| slot < a).collect();
    (Rc::new(before), captured)
}

/// Whether a call of R(A) in `caller`, of the context `calling`, can inline `callee`, whatever its
/// code costs. See Note [Inlined calls].
fn inlines<C>(calling: &Context, caller: &crate::chunk::FunctionBlock<'_, C>, callee: &crate::chunk::FunctionBlock<'_, C>, a: usize) -> bool {
    inlining()
        && calling.inline.len() < MAX_INLINE_DEPTH as usize
        && inline_offset(calling) + a + 1 + callee.max_stack as usize <= MAX_INLINE_SLOTS
        && callee.is_vararg == 0
        && !core::ptr::eq(caller, callee)
        && callee.instructions.items.iter().all(|inst| !matches!(inst.0.Opcode(), Opcode::TAILCALL | Opcode::VARARG))
}

/// What an inlined callee's code costs and its credit. See Note [Inlined calls].
#[derive(Debug, Clone, Copy)]
struct InlineCost {
    cost: usize,
    reused: usize,
}

impl InlineCost {
    fn inlines(self) -> bool {
        self.cost <= MAX_INLINE_COST + REUSED_GUARD_CREDIT * self.reused
    }
}

/// The context an inlined call in `caller`, of R(A) with operand B, enters the callee `proto`
/// with: the entry context a call has, and what the caller knows of the arguments it passes, as
/// the callee's parameters, and of its closure's upvalues, as the callee's own, for the inlined
/// call `frame`. See Notes [Inlined calls] and [Upvalue paths].
fn inline_entry<C>(caller: &Context, proto: &crate::chunk::FunctionBlock<'_, C>, a: usize, b: usize, frame: InlineFrame) -> Context {
    let mut entry = entry_context(caller, proto, a, b);
    let args = a + 1..a + 1 + (proto.param_count as usize).min(entry.types.len());
    let shifted = |slot: usize| args.contains(&slot).then(|| slot - a - 1);
    // The caller's hash keys, at their indexes, in the caller's witnesses: a parameter's are its
    // argument's, with its shape, and any other's are the caller's own, which no slot of the
    // callee names. See Note [Inlined calls].
    let slots = entry.types.len();
    entry.hkeys = caller.hkeys.iter().map(|hkey| {
        let mut hkey = hkey.clone();
        hkey.hazards = (0..slots).map(|slot| args.contains(&(a + 1 + slot)) && hkey.checked(a + 1 + slot)).collect();
        if !hkey.orphan() {
            hkey.idx = shifted(hkey.idx).unwrap_or(OUTER);
        }
        hkey
    }).collect();
    for slot in args.clone() {
        if let CType::Shape(of, hrefs) = caller.slot(slot) && entry.types[slot - a - 1] == CType::Type(of) {
            entry.types[slot - a - 1] = CType::Shape(of, hrefs);
        }
    }
    let params = 0..(proto.param_count as usize).min(entry.types.len());
    let fields: Vec<[Label; 1]> = (0..proto.upval_count).map(|n| [Label::Upvalue(n)]).collect();
    let map: Vec<(Root, Loc)> = params
        .filter(|&param| entry.types[param] != CType::Type(LType::Nil))
        .map(|param| (Root::Slot(param as u16), Loc::root(Root::Slot((a + 1 + param) as u16))))
        .chain(fields.iter().enumerate().map(|(n, path)| (Root::Upvalue(n as u8), Loc { root: Root::Slot(a as u16), path })))
        // A callee's globals are its caller's. See Note [Field facts].
        .chain(caller.values.roots().filter(|root| matches!(root, Root::Global(_))).map(|root| (root, Loc::root(root))))
        // What it learns of the values it was passed, its return gives its caller. See Note [Inlined
        // calls].
        .chain(args.clone().map(|arg| (Root::Arg((arg - a - 1) as u8), Loc::root(Root::Slot(arg as u16)))))
        .collect();
    entry.values = caller.closing(0).view(&map);
    entry.inline = caller.inline.iter().cloned().chain([frame]).collect();
    entry
}
/// The context a call in `caller`, of R(A) with operand B, enters the callee
/// `proto` with. See Note [Call sites].
fn entry_context<C>(caller: &Context, proto: &crate::chunk::FunctionBlock<'_, C>, a: usize, b: usize) -> Context {
    let slots = proto.max_stack as usize;
    let mut entry = Context::new(slots);
    let passed = if b != 0 { Some(b - 1) } else { caller.top.map(|top| top.saturating_sub(a + 1)) };
    let Some(passed) = passed.filter(|_| proto.is_vararg == 0) else { return entry };
    for param in 0..(proto.param_count as usize).min(slots) {
        entry.types[param] = if param >= passed {
            CType::Type(LType::Nil)
        } else {
            match caller.slot(a + 1 + param) {
                CType::Shape(of, _) => CType::Type(of),
                ctype => ctype,
            }
        };
    }
    entry
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum CType {
    /// Any value.
    Unknown,
    Type(LType),
    /// A number in either encoding, `Integer` or `Double`.
    Number,
    /// A table, or a userdata (Note [Userdata fields]), with these hash keys.
    Shape(LType, SmallVec<[HashRef; 4]>),
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
    pub(crate) fn accepts(&self, other: &CType) -> bool {
        match (self, other) {
            (a, b) if a == b => true,
            (CType::Unknown, _) => true,
            (CType::Number, CType::Type(LType::Integer | LType::Double)) => true,
            // A shape is above one with more hash keys: code knowing fewer of a table's keys is
            // correct where more are known, the context's hash keys accepting index by index.
            (CType::Shape(a, mine), CType::Shape(b, theirs)) => a == b && mine.iter().all(|href| theirs.contains(href)),
            // A shape or a function's identity is below its table or closure.
            (CType::Type(a), b) => b.as_ltype() == Some(*a),
            _ => false,
        }
    }

    /// The type's height in the lattice: how much it tells.
    fn depth(&self) -> usize {
        match self {
            CType::Unknown => 0,
            CType::Number => 1,
            CType::Type(LType::Integer | LType::Double) => 2,
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
        } else if CType::Number.accepts(self) && CType::Number.accepts(other) {
            CType::Number
        } else {
            match (self.as_ltype(), other.as_ltype()) {
                (Some(a), Some(b)) if a == b => CType::Type(a),
                _ => CType::Unknown,
            }
        }
    }

    /// The representation every value of this type has, if one does: what a
    /// shape or a function's identity is of, losing it.
    pub(crate) fn as_ltype(&self) -> Option<LType> {
        match self {
            CType::Unknown | CType::Number => None,
            CType::Type(ty) => Some(*ty),
            CType::Shape(of, _) => Some(*of),
            CType::NativeFunction(_) | CType::LuaFunction(_) => Some(LType::Closure),
        }
    }
}

impl std::fmt::Display for CType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CType::Unknown => write!(f, "?"),
            CType::Type(ltype) => ltype.fmt(f),
            CType::Number => write!(f, "number"),
            CType::Shape(of, shape) => write!(f, "{}shape({})", if *of == LType::Table { "" } else { "userdata " }, shape.iter().map(|hr| hr.0.to_string()).intersperse(",".to_string()).collect::<String>()),
            CType::NativeFunction(func) => write!(f, "native_fn({:?})", func),
            CType::LuaFunction(lclos) => write!(f, "fn({:?})", lclos.as_ptr()),
        }
    }
}

// Note [Integers]
// ~~~~~~~~~~~~~~~
// A number is in the integer or the double encoding (Note [Integer encoding]), and its tag says
// which. The specialization context tracks its knowledge potentially fuzzier than that:
// `CType::Type(LType::Integer)` is a number in the integer encoding, `CType::Type(LType::Double)`
// one in the double encoding, and `CType::Number` a number in either, which no value's
// representation is. As the value carries its encoding, a context knowing less of it needs no
// code: a jump into a version typing a slot `Number` or `Unknown` enters it as it is, and generic
// code (a table, an upvalue, a native, a return) reads either.
//
// A constant an i32 holds exactly is an integer, unless it meets a double (Note [Widening]). Any
// other number is a double unless something narrows it to an integer, as LuaJIT narrows: a
// native's result and the generic paths' arithmetic are doubles. What narrows is a loop (below), a length, a bit
// operation, a typed integer op on integers, and `math.floor`, `math.ceil` and `math.abs` of a
// number they keep whole, each until its result first overflows (Note [Optimistic ops]). A constant an i32 holds exactly is a compile-time
// value either encoding can hold, so to an op asking for an integer (a constant guard for one,
// `IntegralK`) it is one: an integer register plus such a constant, or such a constant as an
// array key, is an integer op.
//
// Numeric operations should attempt to specialize on their operands' encoding where
// they can, so they don't require decoding at runtime. The integer encoding can only store small
// numbers, and so the result of arithmatic operations must be careful to check for overflow or
// non-integer results, with guards potentially transitioning the static type back to double.
//
// Discovery finds out the encoding with the type: a discovery thunk forced on a number types its
// slot `Integer` or `Double` and guards that, potentially from existing fuzzy information. A guard
// continues its generator a `SubPc` step for each level of the lattice it tests down to, so that
// both initial discovery and incremental refinement end at the same SubPc and can potentially
// reuse existing versions. See Note [Subblocks].
//
// Care must be taken with this, because the specializer tracking both encoding as well as the
// fuzzy "number" means that discovering *which* encoding causes the static type context to
// transition, potentially causing a new version of a block to be emitted. In practice this
// translates to eagerly typing FORPREP induction variables as integers, so that they aren't only
// discovered partway through a loop and cause recompilation, and arithmetic operations discover
// the types of their operands in a non-eager way that keeps their types stable when not demanded.
// FORPREP promotes each of its index, limit and step that is a double an i32 holds exactly to the
// integer encoding, as an optimistic op (Note [Optimistic ops]), so a loop over doubles that are
// whole, as every constant bound is, is an integer loop, and its index an array key.

/// Where a guard for `expected` continues its generator, with what, when the value's type is
/// `found`. Each step down the lattice translates into one SubPc step, so that continuing the
/// generator at different `found` but to the same `expected` reach the same state and so can be
/// potentially deduplicated. See Note [Subblock].
pub(crate) fn navigate(pc: SubPc, expected: &CType, found: &CType) -> (SubPc, ResumeArg) {
    match expected {
        // `Integer` is two levels, a `Number`, then the encoding; every `CType::Type` one. See Note [Integers].
        CType::Type(LType::Integer) if !CType::Number.accepts(found) => (pc.next_false(), ResumeArg::Failed),
        CType::Type(LType::Integer) if *found == CType::Type(LType::Integer) => (pc.next_true().next_true(), ResumeArg::Matched),
        CType::Type(LType::Integer) => (pc.next_true().next_false(), ResumeArg::Failed),
        expected if expected.accepts(found) => (pc.next_true(), ResumeArg::Matched),
        _ => (pc.next_false(), ResumeArg::Failed),
    }
}

// Note [Global caches]
// ~~~~~~~~~~~~~~~~~~~~
// Each GETGLOBAL and SETGLOBAL has a cache (`GlobalCache`) of where its global's
// value is in the global environment, so an access is a compare and a load, not
// a hash lookup. Where a global's value is goes in no context; what a guard found
// of its value does, as a fact about the global (Note [Field facts]), which a
// join keeps only where both paths have it.
//
// A cache holds the entry's address and `env_moves()` when it found it. The
// entry stays at that address until the environment's entries move, which only
// an insert of a new key (reallocating) or a clear does; those bump the counter
// (`Table::insert_hash`, `Table::clear_hash`), and a cache whose count differs
// looks the key up again. The table's epoch can't serve: a store changing a
// global's type bumps it too, which would miss every cache in a loop storing a
// global.
//
// The cache has a stable address (the specializer owns it), which is the window
// op's hole, so refilling it needs no change to compiled code.
//
// String method lookups are cached the same way (Note [String methods]). Inserting into the
// strings' table, or clearing it, moves its entries too, and bumps the same counter.
//
// A register may hold the environment too (`_G`, or an alias of it), with hash
// keys whose field types rely on its epoch. So a SETGLOBAL changing a value's
// type bumps the epoch, and makes hash keys of the same key check it again.

// Note [Field types]
// ~~~~~~~~~~~~~~~~~~
// A hash key's `known_type` is the type of its field's value, including a
// number's encoding. It has to be checked per table: `href_init` finds the key in
// whatever table reaches the code, and tables of the same shape can hold
// different types there (one table's field an integer, another's a double).
//
// So `href_init` is followed by a guard of the field's type, read through its
// witness (`GuardWitness`): the href thunk guards the type it finds when forced,
// and continues the instruction knowing it, for a load's slot and a store's
// `Retype` alike. A failure finds the field's type and guards that in turn, each
// type going on in a version of its own. `href_init` is itself a guard, of the
// key's place in the table, and its failure path, finding the key elsewhere,
// meets its pass at the field's guard.
//
// The type stays valid while the witness has the table's current epoch, because
// anything that changes a field's type bumps the epoch: a witness store per its
// `Retype` (never `Same` for an unknown type), and a generic store whose value's
// type differs. When an access finds the epoch changed, `HashGuard` checks the
// type again; if that fails it falls back to a fresh href, which guards the type
// again and can rejoin the blocks already compiled for it.
//
// Joining contexts that know different types of a field (an integer on one way
// in, a double on another) keeps its hash key, of no stable type (`Mixed`): a
// load through it guards the loaded slot instead (`FieldType`), and the type
// found becomes the hash key's again. A hash key's type is `None` only while its
// index is free.
//
// A field's type is only ever a representation: a shape or a function's identity
// describes a register, not a field.
//
// A field's hash key on a slot has the same index on every path through the
// function's code whose witnesses it uses, and an inlined callee's on a table it
// was passed its caller's slot's: the index the first hash key for that field and
// slot was given. So paths learning the same fields in another order, as code
// runs before and after its calls are inlined, reach the same contexts, and a
// context knowing some of them reaches the versions compiled knowing fewer (Note
// [Version compatibility]). A path finding something else at that index gives the
// field a free one instead.

// Note [Table metatables]
// ~~~~~~~~~~~~~~~~~~~~~~~
// A table can have a metatable (`setmetatable`). When a lookup finds no value for a key, or a
// nil one, it continues in the metatable's `__index` table, and so on down the chain, as Lua's
// does. Only a table `__index` is supported, and no `__newindex`: setting a metatable that has
// one, or storing to a `__newindex` key, is not implemented.
//
// Every load that can find nil continues down the chain. The generic lookup does. A global
// leaves for it on a cold path when it loads nil. An array element exits when it loads nil, and
// the code after that exit looks the key up down the chain. An array load whose kind is known
// not to be nil can't find nil, and has no such exit.
//
// A load with a constant key follows the chain with hash keys. When its table lacks the key, or
// has it nil, and has an `__index` table, the load uses two more hash keys: one for the
// metatable's `__index` field, and one for the key in that table, which knows the type of the
// field found there. Each has its own witness and epoch check like any other, and finds its
// table through the witness before it, so a table with no metatable pays nothing for chains.
// The load continues this way for a bounded number of hops. A table without the key at the
// end of the chain is a load the hash keys don't handle. Once the generator knows of a chain,
// a later load of that key checks every hash key in it, and if any check fails the whole chain
// is found again. The chain's hash keys belong to its first one's register and go together.
// A load never uses a hash key whose field it knows is nil: the field might be found down a
// chain.
//
// Stores set the table's own field, so they never follow a chain.
//
// A table's epoch changes whenever what a lookup through it could find changes: a key inserted,
// its metatable set, or its `__index` field stored to, whatever the value (a store usually keeps
// the epoch when it keeps the field's type).

// Note [String methods]
// ~~~~~~~~~~~~~~~~~~~~~~
// In Lua, every string shares one metatable whose `__index` is the `string` library, so
// `s:lower()` calls `string.lower`. We look a string's fields up in that table (the strings'
// table) directly, with no further `__index` chain.
//
// A lookup with a constant key, such as a method call, goes through a per-site cache, like a
// global's (Note [Global caches]). We don't use hash keys for this: a hash key belongs to a
// register, and a register that holds a different string each time (a loop variable, say)
// would have to find the key again every time. The table is the same for every string, so
// caching the lookup site is enough.
//
// A lookup with any other key searches the table.

// Note [Userdata fields]
// ~~~~~~~~~~~~~~~~~~~~~~
// A userdata has no fields of its own: a field read from one is its metatable's `__index`
// table's, read raw, with no chain past it. So a register holding a userdata has hash keys as a
// table's register does, in that table's hash part, and a shape of its own representation
// (`CType::Shape`), which no table guard accepts. A userdata's metatable is fixed when it's
// made, but its metatable's `__index` is an ordinary field: what reaches the table, from
// `href_init` and from every epoch check, reads it again, and a userdata without an `__index`
// table has no hash keys, as a table without the key.
//
// That table can change with no write to the register, so a witness records which table it's into,
// and an epoch check fails for another table as for another epoch (Note [Hash witnesses]). A check
// is made where one would be for a table, and also after a store through a hash key into an
// `__index` field, which only makes hash keys of the same key check again; a store into a hash
// part through no hash key already makes every hash key check again.

/// Whether a jump forgets a type of a register holding no local in scope at
/// its target, which may still be an expression's temporary (`a and b or c`).
fn forgotten(ctype: &CType) -> bool {
    *ctype != CType::Unknown
}

/// Whether a jump to a target where the registers from `live` on hold no local
/// forgets anything of `ctx`: those registers' types (`forgotten`), and the
/// fragile facts about them.
fn forgets(ctx: &Context, live: usize) -> bool {
    (live..ctx.types.len()).any(|idx| forgotten(&ctx.types[idx]) || ctx.values.has(Root::Slot(idx as u16)))
}

// Note [Jumped-to contexts]
// ~~~~~~~~~~~~~~~~~~~~~~~~~
// A jump forgets what it knows of the registers holding no local in scope at its target, so that
// paths differing only in temporaries they are done with share the target's version. A temporary
// can be live across a jump, though: a LOADBOOL that skips the next instruction writes the
// register its pair's other LOADBOOL does, whose path falls through to the same target knowing its
// type, and what the target does with it (return it, pass it) needs it; a CLOSURE's jump past its
// pseudo-instructions leaves its closure in a temporary until it is returned or stored. Such a
// jump keeps what it knows of the register its instruction wrote: its type, and its value's class
// (Note [Value classes] in `classes`), so both ways in agree.

/// Forget, for a jump to a target where the registers from `live` on hold no
/// local, those registers' types and the fragile facts about them, but `kept`'s.
fn forget_dead(owner: &mut Owner, ctx: &mut Context, live: usize, kept: Option<usize>) {
    let dead = (live..ctx.types.len()).filter(|&idx| forgotten(&ctx.types[idx]) && Some(idx) != kept).map(|idx| (idx, CType::Unknown)).collect();
    ctx.set_types(owner, dead);
    for idx in (live..ctx.types.len()).filter(|&idx| Some(idx) != kept) {
        ctx.effect(Effect::Write(idx));
    }
}

// Note [Dynamic guards]
// ~~~~~~~~~~~~~~~~~~~~~~
// A `GuardDynamic` residual's test is a window op that reads its operands and selects its exit, 1
// to pass and 0 to fail (Note [Window exits] in `window`), and is otherwise pure. Its two edges continue the generator at
// different `SubPc`s, resumed with `Matched` or `Failed`, so their versions are told apart by the
// outcome and needn't differ in context: a test can speculate on what no ctype names, like whether
// a key is in a table's array part (`InArray`), for the instruction's next op alone. Nothing
// records it, so nothing invalidates it: the guard tests it each run.
//
// `GuardDynamic` performs biasing of the branch layout towards the first seen
// input that forces compilation of the branch, identical to normal guards.
//
// With feature `no_dynamic_guards`, every such yield
// fails statically instead, to measure the blocks the guards cost (`just
// graph-guards`).

// Note [Narrowing]
// ~~~~~~~~~~~~~~~~
// A double an i32 holds exactly can be narrowed to the integer encoding where an integer pays: a
// loop's index, limit and step, a generic loop's variables, and an array key. `Narrow` of a slot
// the context types `Double` ends its block in a thunk; forced on a double an i32 holds exactly, it
// narrows the slot in place by an optimistic op (`ToInteger`), whose hot way continues with the
// slot an integer and its cold way with it a double, and forced on any other value it continues
// with it a double, no narrowing ever tried at runtime. A slot of any other type isn't narrowed:
// one of unknown type is most often of another type than a double, and narrowing it would end its
// block for nothing. A slot typed `Integer` is one already, at the same `SubPc` as the narrowed hot
// way, so the code after both is one version: in a loop, the first iteration narrows its counter,
// and the rest compute on an integer. A whole constant is loaded as an integer already (Note
// [Widening]): narrowing a slot holding one uses its fact, and nothing more. A slot stored into an
// array part the context knows holds integers is narrowed as a loop's counter is, by its value at
// runtime: a whole double computed elsewhere keeps the array of the integer kind.

// Note [Widening]
// ~~~~~~~~~~~~~~~
// A constant an i32 holds exactly is loaded in the integer encoding: whole numbers a program
// writes are most often counted, indexed and compared as integers, and arithmetic of an integer
// with a double reads the integer as a double (Note [Integers]), at no cost to its other uses.
// Its load introduces a fact that the slot holds the constant, until something writes the slot,
// which records where it was loaded (Note [Contraction]).
//
// Where the constant meets a double it is better loaded as one: where another version at the same
// point, or the join of the versions there, types its slot a double or `Number`, as a sum a loop
// starts from `0` meets the double from its back edge; and where it is stored into an array known
// to hold doubles, which an integer would make mixed. There its load is rebuilt to load it as a
// double, so every path from it computes on the double, and reaches the versions the double
// does. Until the rebuild, a store into an array known to hold doubles widens the slot in place,
// and stores a constant operand in the double encoding.
//
// A use of the constant as an integer that pays for it (a loop's index, limit or step, an array
// key) relies on the fact and consumes it: the slot's type then says what the fact would, and a
// rebuild to a double, which would undo what the use relies on, is refused. A guard finding out
// the slot's type at runtime consumes it too, deciding how the slot is used instead (one the
// context answers decides nothing). A constant no load made, as a promote's guarded value or what
// an operation of constants folds to (Note [Peephole fusion] in `peephole`), has no load to
// rebuild, and isn't consumed. Where the fact is never used, the code it was carried through
// is contracted. A whole constant passed to a function, stored into a table or an upvalue, or
// passed to a native is the integer it was loaded as: a callee's versions, and a table's other
// values, are out of the load's rebuild's reach. One a field store takes as its operand is stored
// as an integer where the field is known to hold integers, so the field keeps its type, and as
// a double anywhere else, where it may be a double the program writes as a whole number.

// Note [Contraction]
// ~~~~~~~~~~~~~~~~~~
// A fact the context carries can be worth nothing: no code relies on it before it is dropped,
// yet every version it reaches is told apart from the one a path without it gets, so code without
// the fact is compiled a second time. A loop's first iteration, entered with a constant its
// counter starts from, is compiled apart from the iterations after, which enter without it, and
// never rejoins them.
//
// A fact introduced where its introduction can be rebuilt records that origin: the block, where
// in it, and the generator there, which can be resumed in the context without the fact. Each
// context the fact flows into shares its set of origins: a version reached by another path with
// an equal fact adds that path's origins, as does a join keeping the fact. Code relying on the
// fact marks its origins used.
//
// When a version is about to be compiled for a context, and a version at the same point differs
// from it only in having more facts, all with origins and none used, the duplicate need not
// exist: those origins are queued for contraction. So too the other way, whichever path comes
// first: where the context differs from a version only in having more facts, all with origins
// and none used, the context drops them, reaching the version, and their origins are queued. So
// too if the context's own facts the version lacks each say otherwise about something one of
// those facts is about, as a slot holding one constant on one path and another on the other:
// neither is worth keeping where they meet, and
// the context drops its own there. So too when the versions at a point are joined: the facts of
// theirs the join drops, all with origins and none used, are worth nothing past it. And when a
// version's slot holding an unused constant holds another type in the context: the version is
// kept for the type, and the constant contracted out of it. A contraction forgets every version carrying
// a fact with one of the origins, and rebuilds each origin's block from where it introduced the
// fact, as if it never had: the code after is compiled again, without the fact, and reaches the
// versions every other path does. Code forgotten is never entered again, but what is already
// running it can finish, as it is correct where the fact holds. So contraction waits until
// neither the interpreter nor a frame returning will run code past an origin's introduction, and
// is dropped if an origin has JIT code, or a fact was used since. The residual where the origin
// introduced the fact then becomes a thunk: code entering the block from its start ends there, as
// the JIT and the trimming below read it, and the residuals after it are dead. Forced, the thunk
// compiles the code from the origin again, as any thunk lays out its code (Note [Thunk patching]
// in `jit`): in place, truncating the dead residuals. Origins sharing a residual, loads the
// peephole held until one was laid out, share its thunk too: the earliest's, whose code loads the
// rest again as each one's contraction decided.
//
// A fact can be rebuilt from the same origin another way: a constant that meets a double (Note
// [Widening]) is loaded as a double instead, so every path from its load computes on the double.
// A store widening it in place still writes the double until the rebuild, which waits and is
// dropped as a contraction is. An origin needn't introduce a fact: an integer op is rebuilt to compute in the
// double encoding once its result doesn't fit (Note [Optimistic ops]).
//
// Rebuilding replaces code, and the blocks only that code reached are then unreachable: nothing
// that runs (the code running, a frame returning, a handler, a rebuilt block) reaches them. JIT code is entered only
// as its block is, so it keeps alive only what it reaches when its block is reached. Versions are
// no roots, as only code that runs finds one again: versions reaching each other, as a caller's and
// the callee's it calls, are reached or not together. An unreachable one is forgotten, as a
// contraction's are, once its point has all the versions it can have and needs the room for one
// more, the oldest first, one for each new version: until then a path reaching one again, as a
// thunk forced into code that finds it, takes it as it is, with its JIT code. A peel makes its
// versions in the order it learns its facts, so the newest knows the most. While code is
// still running in what the replaced code reached, it may reach any of it, so that rebuild's are
// tried again each time a thunk is forced, until none is.
//
// An origin's rebuild is kept for its point in the function: code compiled there again, as a
// rebuild of an origin before it in the same code compiles it again, takes the same answer
// instead of introducing the fact or asking again. An origin is rebuilt once; the fact may be
// introduced again by other paths, which may be contracted in turn. Each contraction replaces code carrying the fact with code that doesn't, so
// it ends, and a fact some code finds a use for before its duplicate appears is kept.

/// Whether an integer op's overflow rebuilds it to compute in doubles (Note [Optimistic ops]);
/// set `LUNACY_NO_OVERFLOW_REBUILD` for no rebuild, to compare.
fn overflow_rebuilds() -> bool {
    static REBUILDS: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var_os("LUNACY_NO_OVERFLOW_REBUILD").is_none());
    *REBUILDS
}

// Note [Optimistic ops]
// ~~~~~~~~~~~~~~~~~~~~~
// An op can do its common case on its hot path and the rest on its cold path (Note [Cold
// stencils] in `window`), and select which it took, 0 or 1. Yielded as `OptimisticExec`, the op
// is followed by a `Branch` to two ways on: its generator continues on the hot one, resumed with
// `Matched`, and on the cold one, behind a thunk, only once it is taken, resumed with `Failed`. So
// the code after the op can know what its common case gives, as an integer op's result in the
// integer encoding (Note [Integers]), while the rarer case still has its result, from the cold
// path, and a way on knowing that instead. Unlike a dynamic guard's test (Note [Dynamic
// guards]), the op is an op: it writes its outputs either way.
//
// An integer op whose result can overflow is laid out the first time it runs, as a guard is: if
// its result doesn't fit for its operands then, it computes in the double encoding, with no
// integer way at all. If it fits, it is the optimistic integer op, from an origin to rebuild it
// from (Note [Contraction]), until its result first overflows: then the op is rebuilt to compute in
// the double encoding, so its result is a double on every path, and the code only its integer
// result reached is unreachable, and forgotten. Values
// that fit only some of the time, as sums of bit operations' results often do, so get one version
// of the code after them instead of one for each encoding they turn up in. An op whose block has
// JIT code by its first overflow keeps both ways.
//
// In JIT code the `Branch` tests no `select`, as a guard's copy tests none (Note [Guard
// stencils] in `window`): the op's hot path falls through to the hot way, as the next block if
// it is laid out next, and its cold stencil, which ends in a jump to its site record's
// continuation (Note [Cold stencils] in `window`), continues at the cold way, laid out after the
// region's blocks, as such an op's record's continuation.

/// The type of a constant, as a value: a number is a double. See Note
/// [Integers].
fn constant_ctype<S: PartialEq + Eq>(k: &crate::chunk::Constant<S>) -> CType {
    match k {
        crate::chunk::Constant::Nil => CType::Type(LType::Nil),
        crate::chunk::Constant::Bool(_) => CType::Type(LType::Bool),
        crate::chunk::Constant::Number(_) => CType::Type(LType::Double),
        crate::chunk::Constant::String(_) => CType::Type(LType::String),
    }
}

/// Whether a constant is a number an i32 holds exactly.
/// Whether a whole constant's slot typed `ty` elsewhere meets a double there, so the
/// constant is better loaded as one. See Note [Widening].
fn meets_double(ty: &CType) -> bool {
    matches!(ty, CType::Type(LType::Double) | CType::Number)
}

fn integral_constant<S: PartialEq + Eq>(k: &crate::chunk::Constant<S>) -> bool {
    matches!(k, crate::chunk::Constant::Number(n) if is_integer(n.0))
}

/// The type of a constant to a guard for `expected`: a number an i32 holds
/// exactly is an integer to a guard for one, which its op then takes as an
/// integer (`IntegerK`), else as `constant_ctype` says. See Note [Integers].
fn constant_ctype_for<S: PartialEq + Eq>(k: &crate::chunk::Constant<S>, expected: &CType) -> CType {
    match expected {
        CType::Type(LType::Integer) if integral_constant(k) => CType::Type(LType::Integer),
        _ => constant_ctype(k),
    }
}

// Note [Version compatibility]
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// A block specialized to a context is correct for any values its types
// describe, so a jump may enter a version whose context *accepts* its own:
// slot by slot the same type or one above it in the lattice
//
//   Unknown  >  Number  >  Integer or Double
//   Unknown  >  each other LType,  Table > a shape,  Closure > a known function
//
// (and a shape is above one with more hash keys). A version for a table in a slot
// is correct for a shape there, and one for a shape for a shape with more hash
// keys: the jump's hash keys on it past the version's are extra keys the version
// doesn't know, as below. The join relies on this, widening shapes to tables. So
// a caller learning a new field of a table, as an inlined callee's hash keys come
// back to it, reaches the versions compiled knowing fewer of its fields.
//
// Hash keys are compared index by index, since the version's blocks read
// witnesses at those indexes. At each index the version's hash key must be the
// jump's key of the same table, with a type accepting the jump's, and may claim
// an aliasing check only if the jump's has done it too. An orphan accepts
// anything, including no hash key. Extra hash keys the jump has beyond the
// version's are simply unknown to it: their witnesses get overwritten.
//
// A bytecode pc's first `MAX_VERSIONS` contexts each get a version. A jump past
// that enters the accepting version that loses the least lattice height; if none
// accepts, it gets a version for the join of its context and every existing
// one's. Where their hash keys differ, the join forgets all shapes and hash
// keys.
//
// Only jumps to a pc go through this. A block continuing a generator inside an
// instruction (a subblock) depends on that generator's own state as well as on
// its context, so it is only entered from the same context. Every cycle goes
// through a jump, so bounding the versions jumps enter bounds the subblocks;
// `HARD_MAX_VERSIONS` enforces it. The versions of a pc for an inlined call's
// site are bounded apart from its others (Note [Inlined calls]).

/// The versions of a pc before jumps to it reuse one. See Note [Version compatibility].
const MAX_VERSIONS: usize = 3;
/// The jumps' targets code goes on at straight on before one is a block's. See Note [Peephole
/// fusion] in `peephole`.
const MAX_CONTINUED: usize = 64;

/// The values one version of a promote tests before it returns its argument
/// unspecialized. See Note [Promoted values].
pub const PROMOTE_VALUES: usize = 8;
/// The values a promote has versions for, past which it promotes no other.
/// See Note [Promoted values].
const PROMOTE_SITE_VALUES: usize = 512;
/// The versions of a pc, or of a point in its instruction, past which
/// specialization panics. See Note [Version compatibility].
const HARD_MAX_VERSIONS: usize = 16;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Context {
    pub types: SmallVec<[CType; 8]>,
    pub hkeys: Vec<HashKey<'static, 'static>>,
    /// The frame's top, as a slot, when the instruction before left it at one
    /// the specializer knows. See Note [Known top].
    pub top: Option<usize>,
    /// What the specializer assumes and no guard checks: what it knows of the values its places
    /// hold. See Note [Fragile information].
    pub values: Values,
    /// The inlined call whose callee's frame this is, if it is one. See Note [Inlined calls].
    pub inline: Vec<InlineFrame>,
    /// The value each promote this path last passed through promoted, by the
    /// promote's pc, in pc order. See Note [Promoted values].
    pub promoted: SmallVec<[(Pc, i32); 2]>,
}

// Note [Promoted values]
// ~~~~~~~~~~~~~~~~~~~~~~~
// `jit.promote(v)` returns `v`, and specializes the code after it to `v`'s value, as a meta-tracer
// does with the values it is told to treat as constants: an interpreter written in Lua promotes
// its program counter and the instruction there, and its dispatch loop's code is compiled once per
// guest instruction, the guest's control flow its edges.
//
// A promote ends its block in a thunk. Forced, it guards its argument equal to the integer it holds
// then (`EqualsK`), and the code past the guard is a version for that value: the context records
// it in `promoted`, by the promote's pc, and that the argument's slot holds it, as a constant. The guard's other way promotes again, so a site seeing
// several values tests them in turn, up to `PROMOTE_VALUES`, past which it returns its argument
// unspecialized. A promote whose argument the context knows is a constant needs no guard.
//
// A site's values are bounded too: it has versions for the first `PROMOTE_SITE_VALUES` values it
// sees, and returns any other unspecialized. Code past a promote is compiled once per value, so
// promoting what takes many values, as a loop's counter, costs a version per value up to there;
// an interpreter's program counter takes one per guest instruction.
//
// A promoted value isn't a fact about a slot: it says which value the path's last pass through a
// promote had, and holds until the path passes through it again, whatever is written since. So it
// is part of a version's identity, as an inlined frame is (`same_point`): versions with different
// promoted values are never compared, joined or counted together, and `MAX_VERSIONS` bounds each
// value's versions apart. That is what makes a loop over an interpreter's instructions one per
// guest instruction: the loop's back edge, though it overwrote the promoted program counter, still
// carries the value of the instruction just run, so the loop's head has a version per guest
// instruction, and the promote there tests only the values seen after that instruction, most
// often one. Promoted values are per activation: a function's entry has none.

// Note [Array kinds]
// ~~~~~~~~~~~~~~~~~~
// A table's array part has a kind: the representations of the values stored in it since it was
// last emptied, one bit each, which every store sets with no test. It is of a single kind when one
// bit is set, and mixed once two are. A kind only widens while the array holds values, so a table
// of a single kind holds only values of it.
//
// The context learns kinds as fragile information, as one representation or mixed (`Kind`); it
// learns them from elements, so never knows an array empty. A load from an array part of known
// kind has that type with no test. Any other load's slot is an element of its table (`ElementOf`),
// and a guard finding out its representation, if the array's kind is that representation, tests
// the array's kind in place of the element's: an element loaded before is covered, as the kind
// only widened since, and the kind is known after (`Kind`). An array that isn't of the element's
// representation has the element tested, as any value. A loop's first iteration learns the kinds
// of the arrays it reads elements of, so its later iterations, versioned for what the back edges
// carry, read them unguarded. The kind of a table an upvalue holds is known as the upvalue's, so
// it holds past each load of the upvalue (Note [Upvalue paths]).
//
// A guard finding out the representation of an element of a mixed array knows that too
// (a `Mixed` kind): it stays mixed however it is stored into, and a store into it needn't
// widen its kind, which no guard then tests.
//
// Every store into an array part widens its kind, but for a value of a kind the context knows the
// array has, or an element of the same array, which its kind covers. A store that widens may be
// into any table the context knows the kind of, through another slot, so it keeps only the known
// kinds of the value's representation. One that doesn't changes no table's kind, so it keeps every
// known kind: an array keeps its kind, and one known to be of another kind isn't the one stored
// into, as an array part has one kind. This is the type-based alias analysis kinds give: stores
// into an array of integers leave what is known of arrays of booleans or functions.

// Note [Fragile information]
// ~~~~~~~~~~~~~~~~~~~~~~~~~~
// Fragile information is speculation the specializer assumes under a closed-world model, with no
// guard to check it: once established, a fact holds until an effect the specializer sees could
// falsify it, where it is dropped without repair. Every effect that could falsify a fact must be
// visible; where the closed world can't be shown to hold, such as across code the specializer
// doesn't see all of it is dropped. The known top (Note [Known top]) is information of this kind.
//
// It is in the context, as what is known of the values its places hold (`Context::values`; Note
// [Value classes] in `classes`), so it is part of every block's key. A block compiled
// relying on a fact is only entered by paths that established it and kept it since, as any path
// reaching a block with an equal context shares it. It is per activation: a function's entry block
// has none, and a call's continuation only what the callee's effects keep (Note [Call effects]).
//
// Effects come from the residuals as they are yielded (`Context::effect`). A window op writes the
// slots its accesses say it writes (`Effect::Write`), an exec those it says it writes, else any
// slot (`Effect::WriteAny`; it runs no Lua code), a call that isn't a window op or a pure native's
// (Note [Library natives] in `library`) is `Effect::Opaque`, and what a residual can't show a
// yield says (`YieldOp::Effect`: SETUPVAL's `Effect::SetUpvalue`). A store into a table is always
// yielded as one, `Effect::ArrayStore` or the hash hazards it sets: an exec's writes are of its own
// frame, and a caller sees only the store (Note [Call effects]).
//
// An effect falsifies what it writes (`Context::effect`): a written place moves to a class of its
// own, and a domain of facts says which other effects its facts survive. A new domain is a variant
// of `Known`, its key, and where it is established.
//
// Now that you have background of what a fragile fact is, why do we have them? LBBV naturally
// peels one interation of loops during compilation; there is no CFG analysis that identifies a
// loop header as such, and so the body is compiled as a normal block, with an initial static
// context. The static context *out* of that loop body, if it is different than the initial
// conditions of the loop, cause a second version of the loop body to be compiled, and this
// continues to fixpoint (but usually only after a single peel).
//
// In order to take advantage of information that was discovered in the peeled loop, we want to
// populate the context with as much information as we can so that the *second* version may take
// advantage of it. However, we don't want to carry around the information in a way that is
// sensitive to being individually invalidated: if we had a set of information `N` wide, a loop
// carrying one invalidation per backwards edge may drop a single fact from the set at a different
// position each time, and cause `2^n` combination repeatedly compiling the same loop.
//
// Instead the versions of a pc that differ only in their facts are kept ordered by inclusion,
// domain by domain (each key of `Known`, and the equalities), each one's knowledge in a domain
// within the next's, and a context reaching the pc forgets whatever it knows that would break that
// order. Forgetting is always sound, since a version relying on less accepts any context knowing
// more, and n facts of a domain then give at most n + 1 versions for it. Domains are kept apart
// so that facts of one, established and lost on their own schedule, never cost another's: a fact
// is forgotten in one domain alone, and a class split keeps every fact it had. A join of versions
// keeps what a version knowing nothing in a domain doesn't know there.
//
// Which facts a path keeps depends on the order paths are compiled in. Facts established before a
// loop's paths diverge reach every back edge, and are kept by all of them; a path that establishes
// more than an existing version keeps them in a version of its own; and a path whose facts are
// incomparable with one compiled before it keeps only those the two share.

/// What the values in a place are: all of one representation, or not. A known
/// array part's kind (Note [Array kinds]), or a hash key's field's type (Note
/// [Field types]).
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Kind {
    Of(LType),
    Mixed,
}

impl Kind {
    /// Whether a value of representation `t` may be one of this kind.
    pub fn holds(self, t: LType) -> bool {
        self == Kind::Of(t) || self == Kind::Mixed
    }

    /// The type of a value of this kind.
    pub fn ctype(self) -> CType {
        match self {
            Kind::Of(t) => CType::Type(t),
            Kind::Mixed => CType::Unknown,
        }
    }
}

impl std::fmt::Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Kind::Of(t) => t.fmt(f),
            Kind::Mixed => write!(f, "mixed"),
        }
    }
}

// Note [Field facts]
// ~~~~~~~~~~~~~~~~~~
// A table's hash field and a global are places as an upvalue is (Note [Value classes] in
// `classes`): a global a root, and a field an edge from the table's class, each by its name. A
// slot loaded from one is in its class, so what a guard finds of either is known of both, and a
// load needs no guard one before it passed: a global library's functions, or a machine's stacks
// kept in its fields, are known after their first guards. Only a table or a function is kept so: a
// load of anything else has only its type to guard, and its class would only tell versions apart.
// An inlined callee's globals are its caller's, and its parameters' fields its arguments'.
//
// A store with a key of a name may be into any table, the environment included, so it forgets
// every field and the global of that name, and one with an unknown key all of them.

// Note [Upvalue paths]
// ~~~~~~~~~~~~~~~~~~~~
// A fact about an upvalue is one about the value it holds (Note [Value classes] in `classes`): the
// running function's own upvalue j is a root, and upvalue n of a closure is a field of the
// closure's class. Only a closure's prototype is known (what its identity guard compares), not
// the closure, so what is known of its upvalues is known of their values, not of its cells.
//
// A set of the running function's upvalue j makes it hold the value stored, and forgets every
// closure's upvalue fields but those open into the frame: cells are shared, and any of them may be
// j's, but none open into the frame is one of the running function's own. Setting another
// closure's upvalue is a call, whose effects say whether it set any (Note [Call effects]).
//
// A closure made here knows its cells. One it captured from a slot is that slot while it is open
// (an open field), so a write to the slot is one to the upvalue, until a CLOSE or the frame's end
// closes it: from then on it holds the value the slot had, with the slot's type. One it captured
// from the running function's upvalue holds that upvalue's value. A slot only the one closure
// captured is closed into a sealed cell, which only that closure's code reaches: inlined, its sets
// of the cell are of that cell alone, and falsify nothing else; a set of some unknown upvalue may
// be the closure's, and forgets it.
//
// Fields carry facts across inlined calls (Note [Inlined calls]). The callee enters with its own
// upvalue n holding what the closure's field n does, and its return gives the closure's fields
// what its own upvalues then hold, at a place of the caller's still holding the closure, and the
// slots its results go to what it knows of its results, a closure it made included. A caller
// making several calls of one closure learns at its first inlined call what every later one then
// knows.
//
// A slot loaded from an upvalue holds its value, so what either learns the other knows: the
// value's type (`Known::Type`) and, for a table, its array part's kind (`Known::Kind`). So a table
// an upvalue holds, loaded again each time it's used, keeps the kind a guard found once, until
// the upvalue is set or a store into some array part widens kinds.

/// What is known of a value, besides the type the slots holding it have: an upvalue's value's type
/// (`Type`, Note [Upvalue paths]), a table's array part's kind (`Kind`, Note [Array kinds]), and a
/// number constant an i32 holds exactly, with where it was loaded (`Constant`, Note [Widening]).
/// Each is a domain of its own. See Notes [Fragile information] and [Value classes] in `classes`.
#[derive(Clone)]
pub enum Known {
    Type(CType),
    Kind(Kind),
    Constant { value: i32, origins: Option<Origins> },
    /// The value is the table, boxed, and it is watched. See Note [Watched tables].
    Watched(u64),
    /// The value, boxed. See Note [Frozen tables].
    Value(u64),
    /// The value is a table that isn't watched. See Note [Watched tables].
    Unwatched,
    /// The value is no other class's known so. See Note [Disjoint tables].
    Unique,
}

/// The keys of `Known`'s domains.
pub const TYPE: u8 = 0;
pub const KIND: u8 = 1;
pub const CONSTANT: u8 = 2;
pub const WATCHED: u8 = 3;
pub const VALUE: u8 = 4;
pub const UNWATCHED: u8 = 5;
pub const UNIQUE: u8 = 6;
const KEYS: [u8; 7] = [TYPE, KIND, CONSTANT, WATCHED, VALUE, UNWATCHED, UNIQUE];

/// What a context knows of values. See Note [Fragile information].
pub type Values = crate::classes::Classes<Known>;

impl Known {
    /// Where code introduced it, which can be rebuilt from there without it. See Note
    /// [Contraction].
    fn origins(&self) -> Option<&Origins> {
        match self {
            Known::Constant { origins, .. } => origins.as_ref(),
            _ => None,
        }
    }
}

// The origins are where a fact came from, not what it says: versions are told apart only by the
// fact.
impl PartialEq for Known {
    fn eq(&self, other: &Known) -> bool {
        match (self, other) {
            (Known::Type(a), Known::Type(b)) => a == b,
            (Known::Kind(a), Known::Kind(b)) => a == b,
            (Known::Constant { value: a, .. }, Known::Constant { value: b, .. }) => a == b,
            (Known::Watched(a), Known::Watched(b)) | (Known::Value(a), Known::Value(b)) => a == b,
            (Known::Unwatched, Known::Unwatched) | (Known::Unique, Known::Unique) => true,
            _ => false,
        }
    }
}

impl Eq for Known {}

impl Known {
    /// Whether it survives a trip: it wasn't learned through a watch. See Note [Watched tables].
    fn survives_trip(&self) -> bool {
        !matches!(self, Known::Watched(_))
    }
}

impl std::hash::Hash for Known {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Known::Type(ctype) => (TYPE, ctype).hash(state),
            Known::Kind(kind) => (KIND, kind).hash(state),
            Known::Constant { value, .. } => (CONSTANT, value).hash(state),
            Known::Watched(bits) => (WATCHED, bits).hash(state),
            Known::Value(bits) => (VALUE, bits).hash(state),
            Known::Unwatched => UNWATCHED.hash(state),
            Known::Unique => UNIQUE.hash(state),
        }
    }
}

impl std::fmt::Debug for Known {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Known::Type(ctype) => write!(f, "{ctype}"),
            Known::Kind(kind) => write!(f, "kind {kind:?}"),
            Known::Constant { value, .. } => write!(f, "constant {value}"),
            Known::Watched(bits) => write!(f, "watched {bits:#x}"),
            Known::Value(bits) => write!(f, "value {bits:#x}"),
            Known::Unwatched => write!(f, "unwatched"),
            Known::Unique => write!(f, "unique"),
        }
    }
}

impl crate::classes::ClassFact for Known {
    type Key = u8;
    fn key(&self) -> u8 {
        match self {
            Known::Type(_) => TYPE,
            Known::Kind(_) => KIND,
            Known::Constant { .. } => CONSTANT,
            Known::Watched(_) => WATCHED,
            Known::Value(_) => VALUE,
            Known::Unwatched => UNWATCHED,
            Known::Unique => UNIQUE,
        }
    }
    fn join(&self, other: &Self) -> Option<Self> {
        (self == other).then(|| self.clone())
    }
    fn implies(&self, weaker: &Self) -> bool {
        self == weaker
    }
    fn distinct(&self) -> bool {
        matches!(self, Known::Unique)
    }
}

/// The origins of a fact, shared by every context the fact flows into.
type Origins = Rc<TLCell<TlcOwner, Vec<Origin>>>;

/// Where code introduced a fact, which can be rebuilt from there without it.
/// See Note [Contraction].
type Origin = Rc<TLCell<TlcOwner, OriginState>>;

pub struct OriginState {
    /// Rebuilds the code from the introduction, resuming its generator with
    /// how: without the fact, or with the constant loaded as an integer. Taken
    /// once.
    rebuild: Option<Box<dyn FnOnce(&mut Specializer, &mut Owner, ResumeArg)>>,
    /// The block introducing it, which rebuilding truncates at `offset`.
    block: BlockId,
    offset: usize,
    /// Where in the function it is, whose rebuild's answer is kept for it.
    pc: SubPc,
    /// Whether code relied on the fact, which then isn't contracted.
    used: bool,
}

/// What fragile information an operation may falsify. See Note [Fragile
/// information].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Effect {
    /// The stack slot is written.
    Write(usize),
    /// Any stack slot may be written.
    WriteAny,
    /// The upvalue is set.
    SetUpvalue(usize),
    /// Some upvalue, of any closure, is set.
    AnyUpvalue,
    /// Code the specializer doesn't see runs: every fact is dropped.
    Opaque,
    /// A value of the representation (`None` if not known) is stored in some
    /// table's array part.
    ArrayStore(Option<LType>),
    /// A watched table's watchpoint trips: what was learned through a watch is dropped. See Note
    /// [Watched tables].
    Trip,
    /// A table is watched: no table is known not to be. See Note [Watched tables].
    Watch,
}

// Note [Call effects]
// ~~~~~~~~~~~~~~~~~~~
// What a callee did that its caller can see is a join of effects (`Effects`): the representations
// it stored into some table's array part, whether it set some upvalue, whether it stored into some
// table's hash part (the environment's included), and at the top, opaque: code the specializer
// never saw ran. The callee's own frame is its own, and nothing it does there is seen.
//
// Each prototype has the join of the effects of every residual compiled for it so far
// (`Specializer::effects`), which only grows. It is kept out of the context, so it never makes a
// version of its own: whatever path code for the prototype is compiled on adds to the one join. A
// call adds its callee's effects once its continuation knows them (Note [Call continuations]),
// and opaque where nothing does: a call to a native that isn't pure (Note [Library natives] in
// `library`), a call the call site doesn't specialize, and a continuation that doesn't know the
// return.
//
// A return reads its prototype's join when it runs, and returns it with the id of what it returns
// (`RETURNED | effects << EFFECTS_SHIFT | id`). Code only runs once compiled, so the join then
// covers everything the returning activation did. A continuation guarding on that value knows the
// callee's effects: it continues from the caller's context before the call, less what they may
// have falsified (`Effects::apply`). Once a prototype's join grows, its returns fail the guards of
// continuations compiled for the smaller one, and fall through to new ones.

/// What a callee did that its caller can see, a join as a set of bits. See
/// Note [Call effects].
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Effects(pub u16);

impl Effects {
    pub const NONE: Effects = Effects(0);
    /// Some upvalue is set.
    pub const UPVALUE: Effects = Effects(1 << 8);
    /// Some table's hash part is stored into.
    pub const HASH: Effects = Effects(1 << 9);
    /// Some table is watched.
    pub const WATCH: Effects = Effects(1 << 11);
    /// Code the specializer never saw ran: every other effect too.
    pub const OPAQUE: Effects = Effects(Self::ARRAYS | Self::UPVALUE.0 | Self::HASH.0 | Self::WATCH.0 | Self::OPAQUE_BIT);
    /// The representations stored into some table's array part, as `LType::bit`s.
    const ARRAYS: u16 = {
        let mut bits = 0;
        let mut i = 0;
        while i < Self::REPRESENTATIONS.len() {
            bits |= Self::REPRESENTATIONS[i].bit() as u16;
            i += 1;
        }
        bits
    };
    const OPAQUE_BIT: u16 = 1 << 10;
    /// Every representation a value has, each's bit in `ARRAYS`.
    const REPRESENTATIONS: [LType; 8] = [LType::Nil, LType::Bool, LType::String, LType::Closure, LType::Table, LType::Integer, LType::Double, LType::Userdata];

    pub fn join(self, other: Effects) -> Effects {
        Effects(self.0 | other.0)
    }

    /// `effect` as its function's caller sees it: nothing, for one on the
    /// function's own frame.
    fn of(effect: Effect) -> Effects {
        match effect {
            Effect::Write(_) | Effect::WriteAny => Effects::NONE,
            Effect::SetUpvalue(_) | Effect::AnyUpvalue => Effects::UPVALUE,
            Effect::Opaque => Effects::OPAQUE,
            Effect::ArrayStore(None) => Effects(Self::ARRAYS),
            Effect::ArrayStore(Some(stored)) => Effects(stored.bit() as u16),
            // Its callers' code is replaced as it trips. See Note [Watched tables].
            Effect::Trip => Effects::NONE,
            Effect::Watch => Effects::WATCH,
        }
    }

    /// Drop from `ctx`, a caller's context before a call, what the callee's
    /// effects may have falsified. `captured` are the caller's slots below the
    /// call's its closures captured, which a set upvalue may be.
    fn apply(self, owner: &mut Owner, ctx: &mut Context, captured: &[usize]) {
        if self.0 & Self::OPAQUE_BIT != 0 {
            ctx.effect(Effect::Opaque);
        }
        if self.0 & Self::UPVALUE.0 != 0 {
            ctx.effect(Effect::AnyUpvalue);
            for &slot in captured {
                ctx.effect(Effect::Write(slot));
            }
            ctx.set_types(owner, captured.iter().map(|&slot| (slot, CType::Unknown)).collect());
        }
        if self.0 & Self::HASH.0 != 0 {
            ctx.set_hazards(None, None);
        }
        if self.0 & Self::WATCH.0 != 0 {
            ctx.effect(Effect::Watch);
        }
        for stored in Self::REPRESENTATIONS.into_iter().filter(|stored| self.0 & stored.bit() as u16 != 0) {
            ctx.effect(Effect::ArrayStore(Some(stored)));
        }
    }
}

// Note [Errors]
// ~~~~~~~~~~~~~~
// An error is any value, raised by a native (its `Err`), by `error`, or by the run loop for a
// call of what isn't a function. It is pending on the run's state until the run loop unwinds
// it; JIT code raising one exits to the run loop first, as it does for a trap.
//
// A protected call (`pcall`) is laid out at its call site as a call of its first argument
// between pushing a handler and popping it: the callstack's depth at the call, the slot its
// results go to, how many it wants, and the block the code after it continues at. Unwinding
// pops the innermost handler and the frames above its depth, closing their upvalues as their
// returns would, and continues after the call with false and the error as its results. An
// error with no handler ends the program. `error` adds no position to a message, whatever its
// level.
//
// The code after a protected call knows nothing of its results, and its effects are opaque:
// the call may have stopped anywhere. A `pcall` whose call site doesn't specialize its callee
// has no handler pushed for it, and raises an error instead.

// Note [Known top]
// ~~~~~~~~~~~~~~~~
// A CALL with C = 0 leaves every result from R(A) up, and the frame's top
// (`RunState::top`) past them; the instruction after it, a CALL, RETURN or
// SETLIST with B = 0, takes its operands from there to the top. Lua 5.1 emits
// such a pair for a call that is another call's last argument, as in
// `bor(x, band(y, z))`.
//
// A call run as a native's window op (Note [Native windows])
// returns exactly one result, so after one with C = 0 the context records the
// top as the slot past R(A) (`Context::top`), and a CALL with B = 0 after it
// knows its arguments: it can run as a window op in turn. Every other
// instruction forgets the top, and a version with no top accepts one with a
// top. So that the top in memory is right wherever the context doesn't know it,
// the window op's call stores it too (`SetTop`).

impl Mark for Context {
    fn mark(&self, owner: &Owner) {
        for ctype in &self.types {
            ctype.mark(owner);
        }
        for fact in self.values.all_facts() {
            if let Known::Type(ctype) = fact {
                ctype.mark(owner);
            }
        }
    }
}

impl Context {
    /// A context knowing nothing of `slots` slots.
    pub fn new(slots: usize) -> Self {
        Self {
            types: smallvec::smallvec![CType::Unknown; slots],
            hkeys: vec![],
            top: None,
            values: Values::default(),
            inline: Vec::new(),
            promoted: SmallVec::new(),
        }
    }

    /// The context with its free hash key indexes all alike, and none past its last hash key:
    /// contexts knowing the same hash keys are then equal, whatever was at their free indexes
    /// before. See Note [Version compatibility].
    fn canonical_free(ctx: Rc<Context>) -> Rc<Context> {
        if ctx.free_canonical() {
            return ctx;
        }
        let mut ctx = ctx;
        Rc::make_mut(&mut ctx).canonicalize_free();
        ctx
    }

    /// Whether its free hash key indexes are all alike, and none is past its last hash key.
    fn free_canonical(&self) -> bool {
        self.hkeys.iter().all(|hkey| !hkey.orphan() || *hkey == HashKey::free()) && self.hkeys.last().is_none_or(|hkey| !hkey.orphan())
    }

    /// Make its free hash key indexes all alike, and drop those past its last hash key.
    fn canonicalize_free(&mut self) {
        for hkey in self.hkeys.iter_mut().filter(|hkey| hkey.orphan()) {
            *hkey = HashKey::free();
        }
        while self.hkeys.last().is_some_and(|hkey| hkey.orphan()) {
            self.hkeys.pop();
        }
    }

    /// Whether `self` and `other` are at the same point of the code: in the same
    /// inlined call, past the same promoted values. Versions at different points
    /// are never compared. See Note [Promoted values].
    fn same_point(&self, other: &Context) -> bool {
        self.inline == other.inline && self.promoted == other.promoted
    }

    /// The path's promoted value for the promote at `site`, now `value`. See Note [Promoted values].
    fn promote(&mut self, site: Pc, value: i32) {
        match self.promoted.binary_search_by_key(&site, |&(at, _)| at) {
            Ok(i) => self.promoted[i].1 = value,
            Err(i) => self.promoted.insert(i, (site, value)),
        }
    }

    fn tostring(&self, owner: &Owner) -> String {
        format!("context([{}], hkeys: {}, fragile: {:?}{})",
            self.types.iter().map(|t| format!("{}", t)).intersperse(",".to_string()).collect::<String>(),
            self.hkeys.iter().map(|hk| hk.tostring(owner)).intersperse(",".to_string()).collect::<String>(),
            self.values,
            if self.promoted.is_empty() { String::new() } else { format!(", promoted: {:?}", self.promoted) },
        )
    }

    /// Drop what `effect` may falsify. See Notes [Fragile information] and [Upvalue paths].
    fn effect(&mut self, effect: Effect) {
        // A set of a sealed cell is of that cell alone. See Note [Upvalue paths].
        if let Effect::SetUpvalue(j) = effect && self.values.sealed(Root::Upvalue(j as u8)) {
            self.values.write(Root::Upvalue(j as u8));
            return;
        }
        match effect {
            Effect::Write(slot) => self.values.write(Root::Slot(slot as u16)),
            Effect::WriteAny => self.values.retain_roots(|root| !matches!(root, Root::Slot(_))),
            Effect::SetUpvalue(j) => {
                self.values.write(Root::Upvalue(j as u8));
                self.values.retain_fields(|label, target| !matches!(label, Label::Upvalue(_)) || matches!(target, Target::Open(_) | Target::Sealed(_)));
            },
            Effect::AnyUpvalue => {
                self.values.retain_roots(|root| !matches!(root, Root::Upvalue(_)));
                self.values.retain_fields(|label, target| !matches!(label, Label::Upvalue(_)) || matches!(target, Target::Open(_)));
            },
            Effect::Opaque => self.values = Values::default(),
            // Any table may be the one stored into: one of kind `kind` keeps it only for a value
            // of that kind, and a mixed one stays mixed.
            Effect::ArrayStore(stored) => self.values.retain_facts(|fact| match fact {
                Known::Kind(kind) => *kind == Kind::Mixed || stored.is_some_and(|stored| *kind == Kind::Of(stored)),
                _ => true,
            }),
            Effect::Trip => self.values.retain_facts(Known::survives_trip),
            Effect::Watch => self.values.retain_facts(|fact| !matches!(fact, Known::Unwatched)),
        }
        self.inlined(Effects::of(effect));
    }

    /// Add `effects` to what the callee's code this is the context of may have done to its
    /// caller, if it is an inlined call's. See Note [Inlined calls].
    fn inlined(&mut self, effects: Effects) {
        if let Some(frame) = self.inline.last_mut() {
            frame.effects = frame.effects.join(effects);
        }
    }

    /// The kind of the array part of the table in slot `table`, if known. See
    /// Note [Array kinds].
    fn array_kind(&self, table: usize) -> Option<Kind> {
        self.kind(Root::Slot(table as u16))
    }

    /// The kind of the array part of the table `table` holds, if known.
    fn kind(&self, table: Root) -> Option<Kind> {
        match self.values.fact(Loc::root(table), KIND) {
            Some(Known::Kind(kind)) => Some(*kind),
            _ => None,
        }
    }

    /// Assume the array part of the table `table` holds has kind `kind`, wherever else the table
    /// is. See Notes [Array kinds] and [Upvalue paths].
    fn learn_kind(&mut self, table: Root, kind: Kind) {
        self.values.learn(Loc::root(table), Known::Kind(kind));
    }

    /// A root holding the table whose array part slot `slot`'s value was loaded from, if known:
    /// a slot, else an upvalue. See Note [Array kinds].
    fn element_of(&self, slot: usize) -> Option<Root> {
        let path = [Label::ElementOf];
        self.values.members(Loc { root: Root::Slot(slot as u16), path: &path }).into_iter().find(|root| matches!(root, Root::Slot(_) | Root::Upvalue(_)))
    }

    /// The running function's upvalue whose value slot `slot` holds, if known.
    fn holds(&self, slot: usize) -> Option<u8> {
        self.values.members(Loc::root(Root::Slot(slot as u16))).into_iter().find_map(|root| match root {
            Root::Upvalue(j) => Some(j),
            Root::Slot(_) | Root::Global(_) | Root::Arg(_) => None,
        })
    }

    /// Whether a trip falsifies something it knows. See Note [Watched tables].
    fn trips(&self) -> bool {
        self.values.all_facts().any(|fact| !fact.survives_trip())
    }

    /// The slot of the table, and the name, of the field hash key `href` names: a string key of a
    /// table's own hash part. In an inlined callee, a caller's table is the parameter it was passed
    /// as, whose shape has its keys. See Note [Field facts].
    fn field_of(&self, href: HashRef) -> Option<(u16, u64)> {
        let hkey = self.hkeys.get(href.0 as usize).filter(|hkey| !hkey.orphan() && hkey.place == Place::Register)?;
        let crate::chunk::Constant::String(name) = &hkey.key else { return None };
        let table = if hkey.idx != OUTER {
            hkey.idx
        } else {
            (0..self.types.len()).find(|&slot| matches!(&self.types[slot], CType::Shape(_, hrefs) if hrefs.contains(&href)))?
        };
        Some((table as u16, name_hash(name.as_bytes())))
    }

    /// Slot `slot` was just loaded from `root` along `path`, a global or a field: it holds its
    /// value, of the type known of it. See Note [Field facts].
    fn loaded(&mut self, slot: usize, root: Root, path: &[Label]) {
        self.values.assign(Root::Slot(slot as u16), Loc { root, path });
        if let Some(Known::Type(ctype)) = self.values.fact(Loc::root(Root::Slot(slot as u16)), TYPE).cloned() && self.types[slot].accepts(&ctype) {
            self.types[slot] = ctype;
        }
    }

    /// A guard found `ctype` in slot `slot`, loaded from field `field` if any: a global or a field
    /// whose value the slot holds holds a value of it too, as does each slot holding its value,
    /// unless its type already tells more. Only of a table or a function: of any other value, the
    /// slot no longer holds the place's, as what it holds would only tell versions apart. See Note
    /// [Field facts].
    fn learn_held(&mut self, slot: usize, field: Option<HashRef>, ctype: CType) {
        let at = Loc::root(Root::Slot(slot as u16));
        let path;
        let field = match field.and_then(|href| self.field_of(href)) {
            Some((table, name)) => {
                path = [Label::Field(name)];
                Some(Loc { root: Root::Slot(table), path: &path })
            },
            None => None,
        };
        let held = self.values.members(at).iter().any(|root| matches!(root, Root::Global(_)))
            || field.is_some_and(|field| self.values.same(at, field));
        if !held {
            return;
        }
        if !matches!(ctype, CType::Type(LType::Table | LType::Userdata) | CType::LuaFunction(_) | CType::NativeFunction(_) | CType::Shape(..)) {
            self.values.write(Root::Slot(slot as u16));
            return;
        }
        for root in self.values.members(at) {
            if let Root::Slot(member) = root && self.types[member as usize].accepts(&ctype) {
                self.types[member as usize] = ctype.clone();
            }
        }
        self.values.learn(at, Known::Type(ctype));
    }

    /// Forget the fields and globals a store with a key named `stored` may change, or with none,
    /// every field and global: any table may be the one stored into. See Note [Field facts].
    fn forget_named(&mut self, stored: Option<u64>) {
        self.values.retain_fields(|label, _| !matches!(label, Label::Field(name) if stored.is_none_or(|stored| name == stored)));
        self.values.retain_roots(|root| !matches!(root, Root::Global(name) if stored.is_none_or(|stored| name == stored)));
    }

    /// Forget the fields a store through hash key `href` may change: those of its key's name, or
    /// with none, every field and global. A key no field names, not a string, is none of them.
    fn forget_fields(&mut self, stored: Option<HashRef>) {
        match stored {
            Some(href) => if let Some(crate::chunk::Constant::String(name)) = self.hkeys.get(href.0 as usize).map(|hkey| &hkey.key) {
                let name = name_hash(name.as_bytes());
                self.forget_named(Some(name));
            },
            None => self.forget_named(None),
        }
    }

    /// Assume the running function's upvalue `upvalue` holds a value of `ctype`, as does each slot
    /// holding its value, unless the slot's type already tells more.
    fn learn_upvalue(&mut self, upvalue: u8, ctype: CType) {
        for root in self.values.members(Loc::root(Root::Upvalue(upvalue))) {
            if let Root::Slot(slot) = root && self.types[slot as usize].accepts(&ctype) {
                self.types[slot as usize] = ctype.clone();
            }
        }
        self.values.learn(Loc::root(Root::Upvalue(upvalue)), Known::Type(ctype));
    }

    /// Slot `slot`'s type is found out at runtime: a fact that it holds a
    /// constant has had its use. See Note [Widening].
    fn used(&mut self, slot: usize) {
        let loc = Loc::root(Root::Slot(slot as u16));
        if self.values.fact(loc, CONSTANT).is_some_and(|fact| fact.origins().is_some()) {
            self.values.forget(loc, CONSTANT);
        }
    }

    /// Mark that code relies on the constant slot `slot` holds, so that it isn't
    /// contracted. See Note [Contraction].
    fn rely(&self, owner: &mut Owner, slot: usize) {
        if let Some(origins) = self.values.fact(Loc::root(Root::Slot(slot as u16)), CONSTANT).and_then(Known::origins) {
            for origin in owner.ro(origins).clone() {
                owner.rw(&origin).used = true;
            }
        }
    }

    /// Add the origins of `other`'s facts to those of the same facts of `self`,
    /// whose code `other`'s paths now reach. See Note [Contraction].
    fn adopt(&self, owner: &mut Owner, other: &Context) {
        for (root, fact) in self.values.rooted() {
            let Some(mine) = fact.origins() else { continue };
            let Some(theirs) = other.values.fact(Loc::root(root), fact.key()).filter(|theirs| *theirs == fact).and_then(Known::origins) else { continue };
            if Rc::ptr_eq(mine, theirs) {
                continue;
            }
            for origin in owner.ro(theirs).clone() {
                if !owner.ro(mine).iter().any(|known| Rc::ptr_eq(known, &origin)) {
                    owner.rw(mine).push(origin);
                }
            }
        }
    }

    /// The number constant slot `slot` holds, if a fact says. See Note
    /// [Narrowing].
    fn constant(&self, slot: usize) -> Option<i32> {
        match self.values.fact(Loc::root(Root::Slot(slot as u16)), CONSTANT) {
            Some(Known::Constant { value, .. }) => Some(*value),
            _ => None,
        }
    }

    /// A slot holding the running function's upvalue `upvalue`'s value, if known.
    fn held(&self, upvalue: usize) -> Option<usize> {
        self.values.members(Loc::root(Root::Upvalue(upvalue as u8))).into_iter().find_map(|root| match root {
            Root::Slot(slot) => Some(slot as usize),
            Root::Upvalue(_) | Root::Global(_) | Root::Arg(_) => None,
        })
    }

    /// How many inlined calls deep the code this is the context of is.
    fn depth(&self) -> usize {
        self.inline.len()
    }

    /// The cell of the running function's upvalue `upvalue`, if it has one. See Note [Upvalue
    /// cells].
    fn upvalue_cell(&self, upvalue: usize) -> Option<usize> {
        (upvalue < UPVALUE_CELLS).then(|| self.depth() * UPVALUE_CELLS + upvalue)
    }

    /// Whether something is known of the running function's upvalue `upvalue`'s value, so that its
    /// cell holds it. See Note [Upvalue cells].
    fn cell_filled(&self, upvalue: usize) -> bool {
        self.values.has(Root::Upvalue(upvalue as u8))
    }

    /// The cells holding their upvalue's value where this is the context: its own frame's its
    /// facts are about, and every one of each caller's it is inlined into, whose facts the
    /// callee's about its callers' upvalues become on its return. See Note [Upvalue cells].
    fn filled_cells(&self) -> u32 {
        let mut cells = 0;
        for upvalue in 0..UPVALUE_CELLS {
            if self.cell_filled(upvalue) {
                cells |= 1 << self.upvalue_cell(upvalue).unwrap();
            }
        }
        let frame = (1u32 << UPVALUE_CELLS) - 1;
        for depth in 0..self.depth() {
            cells |= frame << (depth * UPVALUE_CELLS);
        }
        cells
    }

    /// The type of the running function's upvalue `upvalue`'s value, if known.
    fn upvalue(&self, upvalue: usize) -> Option<&CType> {
        match self.values.fact(Loc::root(Root::Upvalue(upvalue as u8)), TYPE) {
            Some(Known::Type(ctype)) => Some(ctype),
            _ => None,
        }
    }

    /// What is known once the upvalues open into slot `from` and up are closed: each holds the
    /// value its slot had, with the slot's type, but not that it is a constant, which only a
    /// slot's load is rebuilt for (Note [Widening]). See Note [Upvalue paths].
    fn closing(&self, from: usize) -> Values {
        let mut values = self.values.clone();
        for slot in values.open_slots().into_iter().filter(|&slot| slot as usize >= from) {
            let at = Loc::root(Root::Slot(slot));
            if let Some(ctype) = self.value_type(slot as usize) {
                values.learn(at, Known::Type(ctype));
            }
            values.forget(at, CONSTANT);
        }
        values.close(from as u16);
        values
    }

    /// What slot `slot`'s type says of its value wherever else it is, if anything: a shape's hash
    /// keys are the frame's, so a table's is only that it is one.
    fn value_type(&self, slot: usize) -> Option<CType> {
        match self.slot(slot) {
            CType::Unknown => None,
            CType::Shape(of, _) => Some(CType::Type(of)),
            ctype => Some(ctype),
        }
    }

    /// What `self` knows that `other` doesn't, as each root's facts, if that is all: none if it
    /// knows an equality, a field, or a fact only a field reaches, that `other` doesn't. See Note
    /// [Contraction].
    fn past(&self, other: &Context) -> Option<Vec<(Root, Known)>> {
        let mut split = self.values.clone();
        split.lower_partition(&other.values);
        if split != self.values {
            return None;
        }
        let rooted: Vec<(Root, Known)> = self.values.rooted()
            .filter(|&(root, fact)| other.values.fact(Loc::root(root), fact.key()) != Some(fact))
            .map(|(root, fact)| (root, fact.clone()))
            .collect();
        let mut rest = self.values.clone();
        for (root, fact) in &rooted {
            rest.forget(Loc::root(*root), fact.key());
        }
        KEYS.iter().all(|&key| {
            let mut lowered = rest.clone();
            lowered.lower_facts(key, &other.values);
            lowered == rest
        }).then_some(rooted)
    }

    /// Whether `self` and `other` differ at most in fragile information.
    fn alike(&self, other: &Context) -> bool {
        self.types == other.types && self.hkeys == other.hkeys && self.top == other.top && self.same_point(other)
    }

    /// The type of slot `idx`: unknown past the end.
    fn slot(&self, idx: usize) -> CType {
        self.types.get(idx).cloned().unwrap_or(CType::Unknown)
    }

    /// Whether a block specialized to `self` is correct in `other`. See Note
    /// [Version compatibility].
    fn accepts(&self, other: &Context) -> bool {
        self.same_point(other) && self.hkeys.iter().enumerate().all(|(i, hkey)| {
            hkey.orphan() || other.hkeys.get(i).is_some_and(|theirs| hkey.accepts(theirs))
        })
            && (self.top.is_none() || self.top == other.top)
            && self.values.accepts(&other.values)
            && (0..self.types.len().max(other.types.len())).all(|idx| self.slot(idx).accepts(&other.slot(idx)))
    }

    /// The lattice height `self` loses from `other`, which it accepts.
    fn distance(&self, other: &Context) -> usize {
        (0..self.types.len().max(other.types.len())).map(|idx| other.slot(idx).depth() - self.slot(idx).depth()).sum::<usize>()
            + other.values.size().saturating_sub(self.values.size())
    }

    /// Widen `self` to also accept `other`. Hash keys are joined one by one: a
    /// key both have at the same `HashRef`, of the same slot, stays, its field's
    /// type widened to both and checked only for the slots both check (a hazard
    /// either has, the join has). Any other is dropped: left an orphan, which
    /// `accepts` ignores, and forgotten by every shape listing it.
    fn join(&mut self, owner: &mut Owner, other: &Context) {
        let mut dropped: SmallVec<[HashRef; 8]> = SmallVec::new();
        let mut widened: Vec<(usize, CType)> = Vec::new();
        for idx in 0..self.types.len() {
            let joined = self.types[idx].join(&other.slot(idx));
            match (&self.types[idx], &joined) {
                (a, b) if a == b => {},
                // The same table, of which less is known: its hash keys the join's shape lacks go,
                // and the rest stay its own. See Note [Version compatibility].
                (CType::Shape(_, mine), CType::Shape(_, kept)) => {
                    dropped.extend(mine.iter().filter(|href| !kept.contains(href)).cloned());
                    self.types[idx] = joined;
                },
                _ => widened.push((idx, joined)),
            }
        }
        self.set_types(owner, widened);
        if self.top != other.top {
            self.top = None;
        }
        // Domain by domain: a context knowing nothing in one doesn't drop what `self` knows
        // there. See Note [Fragile information].
        if other.values.equalities() > 0 {
            self.values.lower_partition(&other.values);
        }
        for key in KEYS.into_iter().filter(|&key| other.values.knows(key)) {
            self.values.lower_facts(key, &other.values);
        }
        self.values.for_each_fact_mut(|roots, fact| {
            let Known::Constant { origins, .. } = fact else { return };
            let theirs = roots.first().and_then(|&root| other.values.fact(Loc::root(root), CONSTANT)).and_then(Known::origins);
            *origins = match (origins.take(), theirs) {
                (Some(mine), Some(theirs)) => {
                    let mut joined = owner.ro(&mine).clone();
                    joined.extend(owner.ro(theirs).iter().filter(|origin| !owner.ro(&mine).iter().any(|known| Rc::ptr_eq(known, origin))).cloned());
                    Some(Rc::new(TLCell::new(joined)))
                },
                (mine, theirs) => mine.or_else(|| theirs.cloned()),
            };
        });
        for (i, mine) in self.hkeys.iter_mut().enumerate() {
            match other.hkeys.get(i) {
                _ if dropped.contains(&HashRef(i as u8)) => {
                    mine.known_type = None;
                    mine.clear_checks();
                },
                Some(theirs) if theirs.idx == mine.idx && theirs.key == mine.key && theirs.place == mine.place && theirs.chain == mine.chain && mine.known_type.is_some() && theirs.known_type.is_some() => {
                    if mine.known_type != theirs.known_type {
                        mine.known_type = Some(Kind::Mixed);
                    }
                    for (slot, checked) in mine.hazards.iter_mut().enumerate() {
                        *checked &= theirs.hazards.get(slot) == Some(&true);
                    }
                },
                _ => {
                    mine.known_type = None;
                    mine.clear_checks();
                    dropped.push(HashRef(i as u8));
                },
            }
        }
        dropped.extend(self.fix_chains());
        let shapes: Vec<(usize, CType)> = (0..self.types.len())
            .filter_map(|idx| match &self.types[idx] {
                CType::Shape(of, hrefs) if hrefs.iter().any(|href| dropped.contains(href)) => {
                    let kept: SmallVec<[HashRef; 4]> = hrefs.iter().filter(|href| !dropped.contains(href)).cloned().collect();
                    Some((idx, if kept.is_empty() { CType::Type(*of) } else { CType::Shape(*of, kept) }))
                },
                _ => None,
            })
            .collect();
        self.set_types(owner, shapes);
    }

    fn set_types(&mut self, owner: &mut Owner, ty_effects: Vec<(usize, CType)>) {
        for (idx, ty) in ty_effects {
            if idx > self.types.len() {
                self.types.resize(idx + 1, CType::Unknown);
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
            if let CType::Shape(_, shape) = &self.types[idx] {
                for (kidx, key) in self.hkeys.iter_mut().enumerate() {
                    if key.idx != idx { continue; }
                    // Try to migrate
                    let mut migrated = false;
                    for (new_idx, other_type) in self.types.iter().enumerate() {
                        if new_idx == idx { continue; }
                        let CType::Shape(_, other_shape) = other_type else { continue };
                        let hr: u8 = kidx.try_into().expect("too many hkeys");
                        if other_shape.contains(&HashRef(hr)) {
                            warn!("migrating {} to stack slot {}", kidx, new_idx);
                            key.idx = new_idx;
                            migrated = true;
                            break;
                        }
                    }
                    if !migrated {
                        key.known_type = None;
                    }
                }
                // We can only remove hkeys at the end of the array for the same
                // reason of needing stable hash_witness indexes. For interior ones, we
                // can mark them free and try to re-use the index instead of pushing
                // to the array when we need a new HashKey in order to try and re-use
                // the slot (and potentially end up with the same pre-SetTypes context
                // entirely). See Note [Field types].
                self.fix_chains();
                while let Some(_) = self.hkeys.pop_if(|hkey| hkey.idx == idx) { }
            }
            self.types[idx] = ty;
            warn!("set types to {:?}", &self.types);
        }
    }

    /// Keep the hash keys of `__index` chains whole: a chain's hash keys share
    /// its head's register, and go when any of them does. The heads that go,
    /// which shapes may hold. See Note [Table metatables].
    fn fix_chains(&mut self) -> SmallVec<[HashRef; 4]> {
        let mut dropped = SmallVec::new();
        loop {
            let mut changed = false;
            let len = self.hkeys.len();
            let live = |hkeys: &[HashKey], h: HashRef| hkeys.get(h.0 as usize).is_some_and(|hkey| !hkey.orphan());
            for i in 0..len {
                let hkey = &self.hkeys[i];
                let Some(next) = hkey.chain.filter(|_| !hkey.orphan()) else { continue };
                let whole = live(&self.hkeys, next) && match self.hkeys[next.0 as usize].place {
                    Place::Index(link) => live(&self.hkeys, link) && self.hkeys[link.0 as usize].place == Place::Metatable(HashRef(i as u8)),
                    _ => false,
                };
                if !whole {
                    self.hkeys[i].known_type = None;
                    self.hkeys[i].clear_checks();
                    if self.hkeys[i].place == Place::Register {
                        dropped.push(HashRef(i as u8));
                    }
                    changed = true;
                }
            }
            // The register of the chain each hash key down one is in.
            let mut reached: Vec<Option<usize>> = vec![None; len];
            for i in 0..len {
                if self.hkeys[i].place != Place::Register || self.hkeys[i].orphan() {
                    continue;
                }
                let idx = self.hkeys[i].idx;
                let mut at = i;
                while let Some(next) = self.hkeys[at].chain {
                    let next = next.0 as usize;
                    reached[next] = Some(idx);
                    if let Place::Index(link) = self.hkeys[next].place {
                        reached[link.0 as usize] = Some(idx);
                    }
                    at = next;
                }
            }
            for i in 0..len {
                if self.hkeys[i].place == Place::Register || self.hkeys[i].orphan() {
                    continue;
                }
                match reached[i] {
                    Some(idx) => self.hkeys[i].idx = idx,
                    None => {
                        self.hkeys[i].known_type = None;
                        self.hkeys[i].clear_checks();
                        changed = true;
                    },
                }
            }
            if !changed {
                return dropped;
            }
        }
    }

    /// A new hash key: at a free index, or a new one.
    fn alloc_hkey(&mut self, hkey: HashKey<'static, 'static>) -> HashRef {
        let hkey: HashKey<'_, '_> = hkey;
        match self.hkeys.iter().position(|hkey| hkey.orphan()) {
            Some(i) => {
                self.hkeys[i] = hkey;
                HashRef(i as u8)
            },
            None => {
                let hr: u8 = self.hkeys.len().try_into().expect("too many hrefs");
                self.hkeys.push(hkey);
                HashRef(hr)
            },
        }
    }

    /// The hash keys of `head`'s chain, in the order each one's table is
    /// found: `head`, then each `__index` and the hash key it finds. See Note
    /// [Table metatables].
    fn chain_of(&self, head: HashRef) -> SmallVec<[HashRef; 7]> {
        let mut out = smallvec::smallvec![head];
        let mut at = head;
        while let Some(next) = self.hkeys[at.0 as usize].chain {
            if let Place::Index(link) = self.hkeys[next.0 as usize].place {
                out.push(link);
            }
            out.push(next);
            at = next;
        }
        out
    }

    /// How many `__index` hops down its register's chain `href`'s table is.
    fn chain_depth(&self, href: HashRef) -> usize {
        let mut depth = 0;
        let mut at = href;
        while let Place::Index(link) = self.hkeys[at.0 as usize].place {
            depth += 1;
            let Place::Metatable(before) = self.hkeys[link.0 as usize].place else { break };
            at = before;
        }
        depth
    }

    /// Set optimization hazards for a stack slot, potentially scoped to only information which
    /// can alias with a specific hash key, and potentially keeping intact information about a
    /// stack slot.
    /// Make every hash key of `key` check the epoch again.
    pub fn set_key_hazards(&mut self, key: &LConstant<'static, 'static>) {
        for hkey in self.hkeys.iter_mut().filter(|hkey| hkey.key == *key) {
            hkey.clear_checks();
        }
    }

    pub fn set_hazards(&mut self, keep: Option<usize>, href: Option<HashRef>) {
        self.inlined(Effects::HASH);
        // The store changed the field, wherever it is. See Note [Field facts].
        self.forget_fields(href);
        let mut invalidate: Vec<usize> = (0..self.hkeys.len()).collect();
        if let Some(href) = href {
            // If we know we wrote to an href, then we can set hazards only on hkeys
            // that have the same key value: writing to `x.a` may invalidate `y.a`, but never
            // `y.b`.
            let hkey = &self.hkeys[href.0 as usize].key;
            // Writing `__index` may change which table a userdata's fields are in. See Note
            // [Userdata fields].
            let index = matches!(hkey, crate::chunk::Constant::String(s) if s.as_bytes() == b"__index");
            let types = &self.types;
            invalidate = self.hkeys.iter().enumerate()
                .filter(|(i, hk)| hk.key == *hkey || (index && matches!(types.get(hk.idx), Some(CType::Shape(LType::Userdata, _)))))
                .map(|(i, _)| i).collect();
        }
        if let Some(keep) = keep {
            invalidate = invalidate.drain(..).filter(|i| self.hkeys[*i].idx != keep).collect();
        }
        for invalid in invalidate {
            self.hkeys[invalid as usize].clear_checks();
        }
    }
}

pub struct Specializer<'src, 'intern> {
    pub blocks: Vec<Block>,
    /// The function being specialized, or run: the prototype of the running frame's closure.
    pub proto: LProto<'src, 'intern>,
    #[cfg(feature = "jit")]
    pub jctx: JitContext,

    /// The global caches its blocks use, at stable addresses. See Note [Global
    /// caches].
    pub global_caches: Vec<Box<GlobalCache>>,
    pub versions: std::collections::HashMap<
        LProto<'src, 'intern>,
        std::collections::HashMap<(SubPc, Rc<Context>), BlockId, rustc_hash::FxBuildHasher>, InternedHasher>,
    /// The types of the results of each return that knows them, by its id,
    /// and the id of each. See Note [Call continuations].
    pub returns: Vec<Vec<CType>>,
    return_ids: HashMap<Vec<CType>, u32, rustc_hash::FxBuildHasher>,
    /// The join of the effects of the code compiled for each prototype, at a
    /// stable address its returns read. See Note [Call effects].
    effects: std::collections::HashMap<LProto<'src, 'intern>, Box<Cell<Effects>>, InternedHasher>,
    /// Origins of facts to rebuild, with their function and how (`Failed`
    /// without the fact, `Matched` with the constant an integer), once nothing
    /// runs the code rebuilding replaces. See Note [Contraction].
    contractions: Vec<(LProto<'src, 'intern>, Vec<Origin>, ResumeArg)>,
    /// Where the optimistic integer op being laid out was decided to be one, which its first
    /// overflow rebuilds it from. See Note [Optimistic ops].
    encoding: Option<Origin>,
    /// The integer ops the peephole holds. See Note [Peephole fusion] in `peephole`.
    /// The instruction being compiled: its pc, where an exit of what the peephole holds goes on
    /// from, and whether the peephole holds its integer op. See Note [Peephole fusion] in
    /// `peephole`.
    instruction: Option<(Pc, Restart, bool)>,
    /// Whether the next `compile_one` starts the instruction `instruction` is.
    entering: bool,
    /// The instruction an exit of what the peephole held runs again, compiled next, its integer
    /// op not held. See Note [Peephole fusion] in `peephole`.
    unheld: Option<Pc>,
    /// The jumps' targets the code being compiled went on at straight on, by function and context.
    /// See Note [Peephole fusion] in `peephole`.
    continued: Vec<(usize, Pc, Rc<Context>)>,
    /// Where each rebuilt block ends for code entering it from its start. See Note [Contraction].
    cuts: std::collections::HashMap<BlockId, usize, rustc_hash::FxBuildHasher>,
    /// The instruction of the origin whose rebuild is yet to run at each place in a block. See
    /// Note [Contraction].
    rebuilding: std::collections::HashMap<(BlockId, usize), usize, rustc_hash::FxBuildHasher>,
    /// The targets of the code each rebuild replaced, whose blocks only it reaches are yet to be
    /// forgotten. See Note [Contraction].
    trimming: Vec<Vec<BlockId>>,
    /// The rebuilt blocks. See Note [Contraction].
    rebuilt: std::collections::HashSet<BlockId, rustc_hash::FxBuildHasher>,
    /// The versions the trimming found unreachable, forgotten once their point needs the room.
    /// See Note [Contraction].
    unreachable: std::collections::HashSet<BlockId, rustc_hash::FxBuildHasher>,
    /// Each function's points a contraction rebuilt an origin at, with how: code compiled there
    /// again takes the same answer. See Note [Contraction].
    decided: std::collections::HashMap<LProto<'src, 'intern>, std::collections::HashMap<SubPc, ResumeArg, rustc_hash::FxBuildHasher>, InternedHasher>,
    /// Each function's calls a continuation inlined, by the call's point and the callee: the
    /// entry contexts it decided on. See Note [Inlined calls].
    inlined: HashMap<(LProto<'src, 'intern>, SubPc, LProto<'src, 'intern>), Vec<Context>, rustc_hash::FxBuildHasher>,
    /// Each promote's values that have versions, by its function and pc. See Note [Promoted values].
    promoted: HashMap<(LProto<'src, 'intern>, Pc), std::collections::HashSet<i32, rustc_hash::FxBuildHasher>, rustc_hash::FxBuildHasher>,
    /// The index of each field's hash key on each slot of the code of each function its
    /// witnesses are of, and the indexes each function has given. See Note [Field types].
    key_indexes: HashMap<(LProto<'src, 'intern>, usize, usize, Vec<u8>), u8, rustc_hash::FxBuildHasher>,
    next_key_index: HashMap<LProto<'src, 'intern>, u8, rustc_hash::FxBuildHasher>,
    /// The code after each inlined call, its returns continue compiling. See Note [Inlined calls].
    continuations: Vec<Rc<Continuation>>,
    /// Each Lua call's continuation, by where its returns go on. See Note [Watched tables].
    continuation_sites: HashMap<Location, ContinuationSite>,
    /// The watch sites of each watched table, by its address. See Note [Watched tables].
    watches: HashMap<u64, Vec<WatchSite>>,
    /// Each table watch sites know, by its boxed value, until it trips: what a load from it reads
    /// as it compiles. See Note [Frozen tables].
    frozen: HashMap<u64, Tc<Table<'static, 'static>>>,
    /// How many tables each watch site has been compiled for, by prototype and pc.
    watch_versions: HashMap<(usize, usize), usize>,
}

impl<'src, 'intern> Mark for Specializer<'src, 'intern> {
    fn mark(&self, owner: &Owner) {
        for (proto, versions) in &self.versions {
            for (key, blockid) in versions {
                let (subpc, context) = key.deref();
                (*context).mark(owner);
            }
        }
        for types in &self.returns {
            types.iter().for_each(|ty| ty.mark(owner));
        }
        for entries in self.inlined.values() {
            entries.iter().for_each(|entry| entry.mark(owner));
        }
        for continuation in &self.continuations {
            continuation.caller.mark(owner);
        }
        for table in self.frozen.values() {
            table.mark(owner);
        }
    }
}

impl<'src, 'intern> Specializer<'src, 'intern> {
    pub fn new(proto: LProto<'src, 'intern>) -> Self {
        Self {
            blocks: Vec::new(),
            global_caches: Vec::new(),
            versions: HashMap::default(),
            returns: Vec::new(),
            return_ids: HashMap::default(),
            effects: HashMap::default(),
            contractions: Vec::new(),
            encoding: None,
            instruction: None,
            entering: false,
            unheld: None,
            continued: Vec::new(),
            cuts: Default::default(),
            rebuilding: Default::default(),
            trimming: Vec::new(),
            rebuilt: Default::default(),
            decided: Default::default(),
            promoted: Default::default(),
            key_indexes: Default::default(),
            next_key_index: Default::default(),
            continuations: Vec::new(),
            continuation_sites: HashMap::default(),
            watches: HashMap::default(),
            watch_versions: HashMap::default(),
            frozen: HashMap::default(),
            inlined: Default::default(),
            unreachable: Default::default(),
            #[cfg(feature = "jit")]
            jctx: JitContext::new(),
            proto,
        }
    }

    /// The index of field `key`'s hash key on slot `place` where `ctx` is the context, the same
    /// for every path through the code of the function whose witnesses it uses (the one inlined
    /// calls are inlined into): given the first time, from the function's next. A parameter still
    /// holding the table it was passed has its caller's slot's. See Note [Field types].
    fn key_index(&mut self, ctx: &Context, place: usize, key: &LConstant<'_, '_>) -> Option<usize> {
        let crate::chunk::Constant::String(name) = key else { return None };
        let root = ctx.inline.first().map_or(self.proto, |frame| frame.proto as LProto<'src, 'intern>);
        // The slot the key is named by is chosen so that hash keys are confluent: contexts
        // reaching the same point have each field's key at the same index whether the code that
        // learned it was inlined or not. A callee's key on a table it was passed is named by the
        // caller's slot holding it, so it gets the index the caller's own code would give it, and
        // is the caller's key at that index when it comes back on the return.
        let (depth, slot) = match ctx.inline.last().and_then(|frame| frame.owner(ctx, place)) {
            Some(owner) => (ctx.depth() - 1, owner),
            None => (ctx.depth(), place),
        };
        let entry = (root, depth, slot, name.as_bytes().to_vec());
        if let Some(&index) = self.key_indexes.get(&entry) {
            return Some(index as usize);
        }
        let next = self.next_key_index.entry(root).or_insert(0);
        let index = *next;
        *next = next.checked_add(1)?;
        self.key_indexes.insert(entry, index);
        Some(index as usize)
    }

    /// The id of a return of `results`, the same for every return of them. See
    /// Note [Call continuations].
    /// The join of the effects of the code compiled for `proto`. See Note
    /// [Call effects].
    fn effects_of(&mut self, proto: LProto<'src, 'intern>) -> &Cell<Effects> {
        self.effects.entry(proto).or_insert_with(|| Box::new(Cell::new(Effects::NONE)))
    }

    /// Add `effects` to those of the function being specialized. See Note
    /// [Call effects].
    fn join_effects(&mut self, owner: &Owner, effects: Effects) {
        let cell = self.effects_of(self.proto);
        cell.set(cell.get().join(effects));
    }

    fn return_id(&mut self, results: Vec<CType>) -> u32 {
        if let Some(&id) = self.return_ids.get(&results) {
            return id;
        }
        let id = u32::try_from(self.returns.len()).ok().filter(|&id| id < UNKNOWN_RETURN).expect("too many returns");
        self.returns.push(results.clone());
        self.return_ids.insert(results, id);
        id
    }

    /// Create a new block at a Lua bytecode PC
    pub fn block(&mut self, owner: &mut Owner, entry: Pc, ctx: Rc<Context>) -> BlockId {
        let mut pc = entry;

        let block_id = self.new_block(entry);
        self.blocks[block_id.0].context = Some(ctx.clone());
        let subpc: SubPc = SubPc::new(entry);
        self.versions.get_mut(&self.proto).unwrap().insert((subpc, ctx.clone()), block_id);
        #[cfg(feature = "tracing")]
        {
            let context = ctx.tostring(owner);
            crate::tracing::instant("spec", "block", &[
                ("block", block_id.0.into()),
                ("line", self.traced_line(owner).into()),
                ("pc", entry.into()),
                ("context", context.as_str().into()),
            ]);
        }
        self.blocks[block_id.0].cells = ctx.filled_cells();
        self.blocks[block_id.0].promoted = ctx.promoted.clone();
        self.compile(owner, entry, ctx, block_id);
        return block_id;
    }

    pub fn subblock(&mut self, owner: &mut Owner, pc: SubPc, ctx: Rc<Context>, mut coro: Box<Gen>, arg: ResumeArg) -> BlockId {
        // Never another version's, though their contexts be the same, while the peephole holds
        // something: what it holds isn't in the context. See Note [Peephole fusion] in `peephole`.
        if coro.holds_any() {
            let block = self.new_block(pc.0);
            let compiled = self.compile_one(owner, pc, ctx, coro, arg, block);
            self.go_on(owner, compiled, block);
            return block;
        }
        let ctx = Context::canonical_free(ctx);
        if let Some(((_, ectx), &exists)) = self.versions.get(&self.proto).unwrap().get_key_value(&(pc, ctx.clone())) {
            ectx.clone().adopt(owner, &ctx);
            return exists;
        }
        let ctx = self.contractible(owner, pc, ctx);
        if let Some(((_, ectx), &exists)) = self.versions.get(&self.proto).unwrap().get_key_value(&(pc, ctx.clone())) {
            ectx.clone().adopt(owner, &ctx);
            return exists;
        }
        let count: Vec<_> = self.versions.get(&self.proto).unwrap().iter().filter(|((epc, ty), block)| *epc == pc && ty.same_point(&ctx)).collect();
        if count.len() >= HARD_MAX_VERSIONS {
            panic!("too many versions: {:#?}", count);
        }
        // Finish the remainder of the coroutine
        let new_block = self.new_block(pc.0);
        self.blocks[new_block.0].cells = ctx.filled_cells();
        self.blocks[new_block.0].promoted = ctx.promoted.clone();
        self.versions.get_mut(&self.proto).unwrap().insert((pc, ctx.clone()), new_block);
        let compiled = self.compile_one(owner, pc, ctx, coro, arg, new_block);
        self.go_on(owner, compiled, new_block);

        return new_block;
    }

    /// The block a jump to `pc` in `ctx` enters: a version for `ctx`, or one
    /// accepting it, compiled if need be. See Note [Version compatibility].
    pub fn version(&mut self, owner: &mut Owner, pc: Pc, ctx: Rc<Context>) -> BlockId {
        let ctx = Context::canonical_free(ctx);
        #[cfg(feature = "tracing")]
        let requested = ctx.clone();
        let (block, outcome, joined) = self.choose_version(owner, pc, ctx);
        #[cfg(feature = "tracing")]
        self.trace_version(owner, pc, &requested, block, outcome, joined.as_deref());
        let _ = (outcome, joined);
        block
    }

    /// `version`'s block, how it was chosen, and the context joined for it, if
    /// one was: `exact`, a version for the context; `fragile`, one with fewer
    /// fragile facts; `new`, compiled, under `MAX_VERSIONS`; `accepting`, one
    /// accepting it; `joined`, one accepting the join of it and every version;
    /// `joined-new`, that join compiled.
    fn choose_version(&mut self, owner: &mut Owner, pc: Pc, ctx: Rc<Context>) -> (BlockId, &'static str, Option<Rc<Context>>) {
        let subpc = SubPc::new(pc);
        let versions = self.versions.get(&self.proto).unwrap();
        if let Some(((_, ectx), &exists)) = versions.get_key_value(&(subpc, ctx.clone())) {
            ectx.clone().adopt(owner, &ctx);
            self.unreachable.remove(&exists);
            return (exists, "exact", None);
        }
        let ctx = self.contractible(owner, subpc, ctx);
        let versions = self.versions.get(&self.proto).unwrap();
        if let Some(((_, ectx), &exists)) = versions.get_key_value(&(subpc, ctx.clone())) {
            ectx.clone().adopt(owner, &ctx);
            self.unreachable.remove(&exists);
            return (exists, "exact", None);
        }
        if self.versions_at(owner, subpc, &ctx) >= MAX_VERSIONS {
            self.evict(owner, subpc, &ctx);
        }
        let versions = self.versions.get(&self.proto).unwrap();
        let existing: Vec<(Rc<Context>, BlockId)> = versions
            .iter()
            .filter(|((epc, ectx), _)| *epc == subpc && ectx.same_point(&ctx))
            .map(|((_, ectx), block)| (ectx.clone(), *block))
            .collect();
        // Versions differing only in fragile information are, kind by kind of
        // fact, a chain of subsets, each version's facts of the kind in the
        // next's: `ctx` keeps the most facts of each kind that keep it one. See
        // Note [Fragile information].
        let alike: Vec<&(Rc<Context>, BlockId)> = existing.iter().filter(|(ectx, _)| ectx.alike(&ctx)).collect();
        let mut lowered = (*ctx).clone();
        // The equalities, then each domain of facts.
        for domain in std::iter::once(None).chain(KEYS.into_iter().map(Some)) {
            let lower = |values: &mut Values, towards: &Values| match domain {
                None => values.lower_partition(towards),
                Some(key) => values.lower_facts(key, towards),
            };
            // Whether what `a` knows in the domain, `b` knows too.
            let within = |a: &Values, b: &Values| {
                let mut lowered = a.clone();
                lower(&mut lowered, b);
                lowered == *a
            };
            let size = |values: &Values| match domain {
                None => values.equalities(),
                Some(key) => values.count(key),
            };
            let mut chain: Vec<&Values> = alike.iter().map(|(ectx, _)| &ectx.values).collect();
            chain.sort_by_key(|values| size(values));
            chain.dedup_by(|a, b| within(a, b) && within(b, a));
            let below = chain.iter().rposition(|values| within(values, &ctx.values));
            // Above the top everything is kept; otherwise what is shared with the version above
            // the highest `ctx` knows all of, or with the bottom.
            if let Some(above) = below.map_or(chain.first(), |below| chain.get(below + 1)) {
                lower(&mut lowered.values, above);
            }
        }
        let ctx = if lowered.values == ctx.values {
            ctx
        } else {
            if let Some((ectx, block)) = alike.iter().find(|(ectx, _)| ectx.values == lowered.values) {
                ectx.adopt(owner, &lowered);
                self.unreachable.remove(block);
                return (*block, "fragile", None);
            }
            Rc::new(lowered)
        };
        if existing.len() < MAX_VERSIONS {
            return (self.block(owner, pc, ctx), "new", None);
        }
        let accepting = |ctx: &Context| {
            existing
                .iter()
                .filter(|(ectx, _)| ectx.accepts(ctx))
                .min_by_key(|(ectx, block)| (ectx.distance(ctx), block.0))
                .cloned()
        };
        if let Some((ectx, block)) = accepting(&ctx) {
            ectx.adopt(owner, &ctx);
            self.unreachable.remove(&block);
            return (block, "accepting", None);
        }
        let mut joined = (*ctx).clone();
        for (ectx, _) in &existing {
            joined.join(owner, ectx);
        }
        let joined = Rc::new(joined);
        self.contract_joined(owner, subpc, &existing, &joined);
        if let Some((ectx, block)) = accepting(&joined) {
            ectx.adopt(owner, &joined);
            self.unreachable.remove(&block);
            return (block, "joined", Some(joined));
        }
        if existing.len() >= HARD_MAX_VERSIONS {
            panic!("too many versions at {pc}: {:#?}", existing.iter().map(|(ectx, _)| ectx).collect::<Vec<_>>());
        }
        (self.block(owner, pc, joined.clone()), "joined-new", Some(joined))
    }

    /// How many versions the running function has at `pc` at the same point as `ctx`: for its
    /// inlined call, or for its calls, past its promoted values. See Notes [Inlined calls] and [Promoted
    /// values].
    fn versions_at(&self, owner: &Owner, pc: SubPc, ctx: &Context) -> usize {
        self.versions.get(&self.proto).map_or(0, |versions| versions.keys().filter(|(at, ectx)| *at == pc && ectx.same_point(ctx)).count())
    }

    /// Forget the oldest version at `pc` of the running function, at the same point as `ctx`, the
    /// trimming found unreachable, to make the room a point with all the versions it can have needs
    /// for one more: the others may yet be reused. See Note [Contraction].
    fn evict(&mut self, owner: &Owner, pc: SubPc, ctx: &Context) {
        let versions = self.versions.get_mut(&self.proto).unwrap();
        let dead = versions.iter()
            .filter(|((at, ectx), block)| *at == pc && ectx.same_point(ctx) && self.unreachable.contains(block))
            .min_by_key(|(_, block)| block.0)
            .map(|(key, block)| (key.clone(), *block));
        let mut _evicted: Vec<usize> = Vec::new();
        if let Some((key, block)) = dead {
            versions.remove(&key);
            self.unreachable.remove(&block);
            _evicted.push(block.0);
        }
        #[cfg(feature = "tracing")]
        if !_evicted.is_empty() {
            crate::tracing::instant("spec", "evicted", &[
                ("line", self.traced_line(owner).into()),
                ("pc", pc.0.into()),
                ("blocks", Self::ids(_evicted.iter().copied()).as_str().into()),
            ]);
        }
    }

    /// Queue the origins of the facts versions at `pc` have that `joined`, their join, drops, for
    /// contraction: no code relied on them, and the join's version is the one the code after them
    /// gets. See Note [Contraction].
    fn contract_joined(&mut self, owner: &mut Owner, pc: SubPc, existing: &[(Rc<Context>, BlockId)], joined: &Context) {
        let proto = self.proto;
        let mut origins: Vec<Origin> = Vec::new();
        // Of constants the join types a double: rebuilt as doubles, not dropped.
        let mut widened: Vec<Origin> = Vec::new();
        let mut _duplicates: Vec<usize> = Vec::new();
        for (ectx, block) in existing {
            let Some(extra) = ectx.past(joined) else { continue };
            if extra.is_empty() {
                continue;
            }
            let doubles = extra.iter().all(|(root, fact)| matches!((root, fact), (Root::Slot(slot), Known::Constant { .. }) if meets_double(&joined.slot(*slot as usize))));
            let Some(sets) = extra.iter().map(|(_, fact)| fact.origins()).collect::<Option<Vec<_>>>() else { continue };
            let found: Vec<Origin> = sets.iter().flat_map(|set| owner.ro(set).iter().cloned()).collect();
            if found.iter().any(|origin| owner.ro(origin).used) || found.iter().all(|origin| owner.ro(origin).rebuild.is_none()) {
                continue;
            }
            _duplicates.push(block.0);
            let into = if doubles { &mut widened } else { &mut origins };
            for origin in found {
                if !into.iter().any(|known| Rc::ptr_eq(known, &origin)) {
                    into.push(origin);
                }
            }
        }
        let queued = |origin: &Origin| self.contractions.iter().any(|(_, queued, _)| queued.iter().any(|known| Rc::ptr_eq(known, origin)));
        widened.retain(|origin| !origins.iter().any(|known| Rc::ptr_eq(known, origin)));
        let widens = !widened.is_empty() && !widened.iter().all(queued);
        let drops = !origins.is_empty() && !origins.iter().all(queued);
        if widens {
            self.contractions.push((proto, widened, ResumeArg::Type(CType::Type(LType::Double))));
        }
        if !drops {
            return;
        }
        #[cfg(feature = "tracing")]
        {
            let context = joined.tostring(owner);
            crate::tracing::instant("spec", "contractible", &[
                ("line", self.traced_line(owner).into()),
                ("pc", pc.0.into()),
                ("duplicates", Self::ids(_duplicates.iter().copied()).as_str().into()),
                ("origins", Self::ids(origins.iter().map(|origin| owner.ro(origin).block.0)).as_str().into()),
                ("context", context.as_str().into()),
            ]);
        }
        self.contractions.push((proto, origins, ResumeArg::Failed));
    }

    /// Queue the origins of the facts a version at `pc` has past those of `ctx`,
    /// which is about to get a version of its own, for contraction: if no code
    /// relied on them, the version only duplicates the one `ctx` gets. A fact
    /// of `ctx` about the same thing as one of those, which says otherwise, is
    /// dropped: what `ctx` is then left with is the context the version
    /// contracted to. See Note [Contraction].
    fn contractible(&mut self, owner: &mut Owner, pc: SubPc, ctx: Rc<Context>) -> Rc<Context> {
        let proto = self.proto;
        let mut origins: Vec<Origin> = Vec::new();
        // Of constants meeting a double: rebuilt as doubles, not dropped.
        let mut widened: Vec<Origin> = Vec::new();
        let mut conflicting: SmallVec<[(Root, u8); 2]> = SmallVec::new();
        let mut _duplicates: Vec<usize> = Vec::new();
        // Each duplicate's context, and whether it was one for a constant's slot of another type.
        #[cfg(feature = "tracing")]
        let mut _their: Vec<String> = Vec::new();
        for ((epc, ectx), _block) in self.versions.get(&proto).unwrap() {
            if *epc != pc || !ectx.same_point(&ctx) {
                continue;
            }
            // A version whose slot holding a constant holds another type here: the constant is
            // worth nothing past the point either. See Note [Contraction].
            if !ectx.alike(&ctx) {
                let retyped: Vec<(usize, Known)> = ectx.values.rooted().filter_map(|(root, fact)| match (root, fact) {
                    (Root::Slot(slot), Known::Constant { .. }) if ctx.values.fact(Loc::root(root), CONSTANT) != Some(fact) && ectx.slot(slot as usize) != ctx.slot(slot as usize) => Some((slot as usize, fact.clone())),
                    _ => None,
                }).collect();
                let doubles = !retyped.is_empty() && retyped.iter().all(|(slot, _)| meets_double(&ctx.slot(*slot)));
                let Some(sets) = retyped.iter().map(|(_, fact)| fact.origins()).collect::<Option<Vec<_>>>() else { continue };
                let found: Vec<Origin> = sets.iter().flat_map(|set| owner.ro(set).iter().cloned()).collect();
                if found.is_empty() || found.iter().any(|origin| owner.ro(origin).used) || found.iter().all(|origin| owner.ro(origin).rebuild.is_none()) {
                    continue;
                }
                _duplicates.push(_block.0);
                #[cfg(feature = "tracing")]
                _their.push(format!("{} {}: {}", _block.0, if doubles { "widened" } else { "retyped" }, ectx.tostring(owner)));
                let into = if doubles { &mut widened } else { &mut origins };
                for origin in found {
                    if !into.iter().any(|known| Rc::ptr_eq(known, &origin)) {
                        into.push(origin);
                    }
                }
                continue;
            }
            // The version has every fact `ctx` has but some only `ctx` has, all from origins and
            // none used: `ctx` drops those, reaching the version, and they are contracted.
            if ectx.values.accepts(&ctx.values) && let Some(theirs) = ctx.past(ectx) {
                let Some(sets) = theirs.iter().map(|(_, fact)| fact.origins()).collect::<Option<Vec<_>>>() else { continue };
                let found: Vec<Origin> = sets.iter().flat_map(|set| owner.ro(set).iter().cloned()).collect();
                if theirs.is_empty() || found.iter().any(|origin| owner.ro(origin).used) || found.iter().all(|origin| owner.ro(origin).rebuild.is_none()) {
                    continue;
                }
                _duplicates.push(_block.0);
                #[cfg(feature = "tracing")]
                _their.push(format!("{} lacks: {}", _block.0, ectx.tostring(owner)));
                for (root, fact) in &theirs {
                    if !conflicting.contains(&(*root, fact.key())) {
                        conflicting.push((*root, fact.key()));
                    }
                }
                for origin in found {
                    if !origins.iter().any(|known| Rc::ptr_eq(known, &origin)) {
                        origins.push(origin);
                    }
                }
                continue;
            }
            // `ctx`'s facts the version lacks each contradict one of its own.
            let Some(mine) = ctx.past(ectx) else { continue };
            let mine: SmallVec<[(Root, u8); 2]> = mine.iter().map(|(root, fact)| (*root, fact.key())).collect();
            if !mine.iter().all(|&(root, key)| ectx.values.fact(Loc::root(root), key).is_some()) {
                continue;
            }
            let Some(extra) = ectx.past(&ctx) else { continue };
            if extra.is_empty() {
                continue;
            }
            let Some(sets) = extra.iter().map(|(_, fact)| fact.origins()).collect::<Option<Vec<_>>>() else { continue };
            let found: Vec<Origin> = sets.iter().flat_map(|set| owner.ro(set).iter().cloned()).collect();
            if found.iter().any(|origin| owner.ro(origin).used) || found.iter().all(|origin| owner.ro(origin).rebuild.is_none()) {
                continue;
            }
            _duplicates.push(_block.0);
            #[cfg(feature = "tracing")]
            _their.push(format!("{} unused: {}", _block.0, ectx.tostring(owner)));
            for key in mine {
                if !conflicting.contains(&key) {
                    conflicting.push(key);
                }
            }
            for origin in found {
                if !origins.iter().any(|known| Rc::ptr_eq(known, &origin)) {
                    origins.push(origin);
                }
            }
        }
        let queued = |origin: &Origin| self.contractions.iter().any(|(_, queued, _)| queued.iter().any(|known| Rc::ptr_eq(known, origin)));
        widened.retain(|origin| !origins.iter().any(|known| Rc::ptr_eq(known, origin)));
        let drops = !origins.is_empty() && !origins.iter().all(queued);
        let widens = !widened.is_empty() && !widened.iter().all(queued);
        if drops || widens {
            #[cfg(feature = "tracing")]
            {
                let context = ctx.tostring(owner);
                crate::tracing::instant("spec", "contractible", &[
                    ("line", self.traced_line(owner).into()),
                    ("pc", pc.0.into()),
                    ("duplicates", Self::ids(_duplicates.iter().copied()).as_str().into()),
                    ("origins", Self::ids(origins.iter().chain(&widened).map(|origin| owner.ro(origin).block.0)).as_str().into()),
                    ("context", context.as_str().into()),
                    ("theirs", _their.join(" | ").as_str().into()),
                ]);
            }
        }
        if drops {
            self.contractions.push((proto, origins, ResumeArg::Failed));
        }
        if widens {
            self.contractions.push((proto, widened, ResumeArg::Type(CType::Type(LType::Double))));
        }
        if conflicting.is_empty() {
            return ctx;
        }
        let mut lowered = (*ctx).clone();
        for &(root, key) in &conflicting {
            lowered.values.forget(Loc::root(root), key);
        }
        Rc::new(lowered)
    }

    /// Contract the queued origins of the running function that no code still to
    /// run relies on: the interpreter at `at`, or a frame returning, past where
    /// one was introduced. The versions their facts reach are forgotten, and each
    /// origin rebuilt without its fact. See Note [Contraction].
    fn contract(&mut self, owner: &mut Owner, state: &RunState<'src, 'intern>, at: Location) {
        if !self.trimming.is_empty() || !self.contractions.is_empty() {
            self.rebuild_queued(owner, state, &at);
            self.trim(owner, state, at);
        }
    }

    /// How a contraction rebuilt the origin at `pc` of the running function, if one did: code
    /// compiled there again takes the same answer. See Note [Contraction].
    fn decision(&self, owner: &Owner, pc: SubPc) -> Option<ResumeArg> {
        self.decided.get(&self.proto)?.get(&pc).cloned()
    }

    /// Rebuild the queued origins of the running function that nothing runs past, the interpreter
    /// at `at` or a frame returning: each becomes a thunk compiling the code from there again, and
    /// the blocks the code it replaced reached are to be trimmed. See Note [Contraction].
    fn rebuild_queued(&mut self, owner: &mut Owner, state: &RunState<'src, 'intern>, at: &Location) {
        let proto = self.proto;
        for (of, origins, how) in std::mem::take(&mut self.contractions) {
            if of != proto {
                self.contractions.push((of, origins, how));
                continue;
            }
            let _blocks = Self::ids(origins.iter().map(|origin| owner.ro(origin).block.0));
            let _how = match how {
                ResumeArg::Failed => "drop",
                _ => "double",
            };
            // Relied on since, or rebuilt in code that has its own JIT code.
            let refused = if origins.iter().any(|origin| owner.ro(origin).used) {
                Some("used")
            } else if origins.iter().any(|origin| owner.ro(origin).rebuild.is_some() && self.compiled(owner.ro(origin).block)) {
                Some("compiled")
            } else if origins.iter().all(|origin| owner.ro(origin).rebuild.is_none()) {
                Some("rebuilt")
            } else {
                None
            };
            if let Some(_reason) = refused {
                #[cfg(feature = "tracing")]
                crate::tracing::instant("spec", "contract_refused", &[
                    ("line", self.traced_line(owner).into()),
                    ("origins", _blocks.as_str().into()),
                    ("how", _how.into()),
                    ("reason", _reason.into()),
                ]);
                continue;
            }
            let live: Vec<Origin> = origins.iter().filter(|origin| owner.ro(origin).rebuild.is_some()).cloned().collect();
            let past = |origin: &OriginState, Location(block, off): &Location| *block == origin.block && *off >= origin.offset;
            if live.iter().any(|origin| past(owner.ro(origin), at) || state.callstack.iter().filter_map(|entry| entry.returns_to()).any(|ret| past(owner.ro(origin), ret))) {
                #[cfg(feature = "tracing")]
                crate::tracing::instant("spec", "contract_deferred", &[
                    ("line", self.traced_line(owner).into()),
                    ("origins", _blocks.as_str().into()),
                    ("at", at.0.0.into()),
                ]);
                self.contractions.push((of, origins, how));
                continue;
            }
            let carries = |ctx: &Context| ctx.values.all_facts().any(|fact| {
                fact.origins().is_some_and(|set| owner.ro(set).iter().any(|origin| origins.iter().any(|known| Rc::ptr_eq(known, origin))))
            });
            let versions = self.versions.get_mut(&proto).unwrap();
            let mut _forgotten: Vec<usize> = Vec::new();
            versions.retain(|(_, ctx), block| {
                let keep = !carries(ctx);
                if !keep {
                    _forgotten.push(block.0);
                }
                keep
            });
            _forgotten.sort_unstable();
            #[cfg(feature = "tracing")]
            crate::tracing::instant("spec", "contract", &[
                ("line", self.traced_line(owner).into()),
                ("origins", _blocks.as_str().into()),
                ("how", _how.into()),
                ("offsets", Self::ids(live.iter().map(|origin| owner.ro(origin).offset)).as_str().into()),
                ("forgotten", Self::ids(_forgotten.iter().copied()).as_str().into()),
            ]);
            for origin in live {
                let (block, offset) = (owner.ro(&origin).block, owner.ro(&origin).offset);
                self.trimming.push(Self::targets(&self.blocks[block.0].instructions[offset..]).collect());
                self.rebuilt.insert(block);
                self.decided.entry(proto).or_default().insert(owner.ro(&origin).pc, how.clone());
                let rebuild = owner.rw(&origin).rebuild.take().unwrap();
                rebuild(self, owner, how.clone());
            }
        }
    }

    /// The residuals of `block` that code entering it at `from` runs: from there to its first jump
    /// (past it, only a frame returning into the block runs), or to a rebuild's jump in it if
    /// `from` is before that. See Note [Contraction].
    fn runnable(&self, block: BlockId, from: usize) -> &[Residual] {
        let residuals = &self.blocks[block.0].instructions;
        let end = match self.cuts.get(&block) {
            Some(&cut) if from < cut => cut.min(residuals.len()),
            _ => residuals.len(),
        };
        let from = from.min(end);
        let end = residuals[from..end].iter().position(|residual| matches!(residual, Residual::Jump(_) | Residual::PatchableJump(_))).map_or(end, |jump| from + jump + 1);
        &residuals[from..end]
    }

    /// The blocks `residuals` can go on to.
    fn targets(residuals: &[Residual]) -> impl Iterator<Item = BlockId> + '_ {
        residuals.iter().flat_map(|residual| -> SmallVec<[BlockId; 2]> {
            match residual {
                Residual::Jump(target) | Residual::PatchableJump(target) => smallvec::smallvec![*target],
                Residual::Branch { hot, cold } => smallvec::smallvec![*hot, *cold],
                Residual::Select(targets) => targets.iter().map(|(_, target)| *target).collect(),
                Residual::LuaCall { entry: CallEntry::Block(target), .. } | Residual::TailCall { entry: CallEntry::Block(target), .. } => smallvec::smallvec![*target],
                _ => SmallVec::new(),
            }
        })
    }

    /// Forget the versions of the blocks only code rebuilds replaced reached, of each rebuild whose
    /// replaced code nothing running is in any more: those reachable from the targets of that code
    /// which nothing that runs reaches (the code running or a frame returning, a protected call's
    /// handler, a rebuilt block). The others are tried again later. A block's JIT code keeps alive
    /// only what it reaches when it is reached itself: every way into JIT code is an edge of the
    /// blocks. See Note [Contraction].
    fn trim(&mut self, owner: &Owner, state: &RunState<'src, 'intern>, at: Location) {
        type Blocks = std::collections::HashSet<BlockId, rustc_hash::FxBuildHasher>;
        // Where what runs goes on from: the code running and a frame returning from where they are.
        let running: Vec<(BlockId, usize)> = std::iter::once((at.0, at.1))
            .chain(state.callstack.iter().filter_map(|entry| entry.returns_to()).map(|ret| (ret.0, ret.1)))
            .chain(state.handlers.iter().map(|handler| (handler.after, 0)))
            .collect();
        let mut reached = Blocks::default();
        for targets in std::mem::take(&mut self.trimming) {
            let mut reach = Blocks::default();
            let mut work = targets.clone();
            while let Some(block) = work.pop() {
                if reach.insert(block) {
                    work.extend(Self::targets(&self.blocks[block.0].instructions));
                }
            }
            if running.iter().any(|(block, _)| reach.contains(block)) {
                self.trimming.push(targets);
            } else {
                reached.extend(reach);
            }
        }
        if reached.is_empty() {
            return;
        }
        // What runs reaches, entering each block where it does (`runnable`).
        let live_from = |roots: &mut dyn Iterator<Item = (BlockId, usize)>| {
            let mut live = Blocks::default();
            let mut entered: std::collections::HashSet<(BlockId, usize), rustc_hash::FxBuildHasher> = Default::default();
            let mut work: Vec<(BlockId, usize)> = roots.collect();
            while let Some((block, from)) = work.pop() {
                if entered.insert((block, from)) {
                    live.insert(block);
                    work.extend(Self::targets(self.runnable(block, from)).map(|target| (target, 0)));
                }
            }
            live
        };
        let live = live_from(&mut running.iter().copied().chain(self.rebuilt.iter().map(|&block| (block, 0))));
        #[cfg(feature = "tracing")]
        let _kept_by = format!("running {}, rebuilt {}",
            live_from(&mut running.iter().copied()).iter().filter(|block| reached.contains(block)).count(),
            live_from(&mut self.rebuilt.iter().map(|&block| (block, 0))).iter().filter(|block| reached.contains(block)).count());
        let mut _dropped: Vec<usize> = Vec::new();
        for versions in self.versions.values() {
            for block in versions.values() {
                if reached.contains(block) && !live.contains(block) && self.unreachable.insert(*block) {
                    _dropped.push(block.0);
                }
            }
        }
        _dropped.sort_unstable();
        #[cfg(feature = "tracing")]
        crate::tracing::instant("spec", "unreachable", &[
            ("line", self.traced_line(owner).into()),
            ("reached", reached.len().into()),
            ("dropped", Self::ids(_dropped.iter().copied()).as_str().into()),
            ("waiting", self.trimming.len().into()),
            ("kept_by", _kept_by.as_str().into()),
            ("at", at.0.0.into()),
        ]);
        let _ = owner;
    }

    /// The functions each block reachable from `entry` is in, for the JIT's disassembly: the
    /// lines its function and the functions it is inlined into are defined at, outermost first,
    /// as `725-693` for 693's inlined into 725's. A version's are its context's inlined frames' and
    /// its own; any other block's, the block's whose code reaches it, as a function changes only
    /// at a version (a callee's entry, the code after its return), and `?` if none says.
    #[cfg(feature = "jit_disasm")]
    pub fn inline_chains(&self, entry: BlockId) -> HashMap<BlockId, String> {
        let line = |proto: LProto<'_, '_>| unsafe { (*proto).line_defined }.to_string();
        let chain = |proto: LProto<'_, '_>, ctx: &Context| {
            let mut lines: Vec<String> = ctx.inline.iter().map(|frame| line(frame.proto.cast())).collect();
            lines.push(line(proto));
            lines.join("-")
        };
        let mut versions: HashMap<BlockId, String> = HashMap::default();
        for (proto, at) in &self.versions {
            for ((_, ctx), block) in at {
                versions.insert(*block, chain(*proto, ctx));
            }
        }
        // The entry's, if it isn't a version: the nearest version whose code reaches it.
        let of_entry = versions.get(&entry).cloned().or_else(|| {
            let mut reaches: HashMap<BlockId, Vec<BlockId>> = HashMap::default();
            for (from, block) in self.blocks.iter().enumerate() {
                for target in Self::targets(&block.instructions) {
                    reaches.entry(target).or_default().push(BlockId(from));
                }
            }
            let mut seen = std::collections::HashSet::new();
            let mut work = std::collections::VecDeque::from([entry]);
            while let Some(block) = work.pop_front() {
                if let Some(of) = versions.get(&block) {
                    return Some(of.clone());
                }
                if seen.insert(block) {
                    work.extend(reaches.get(&block).into_iter().flatten().copied());
                }
            }
            None
        });
        let mut chains: HashMap<BlockId, String> = HashMap::default();
        let mut work = vec![(entry, of_entry.unwrap_or_else(|| "?".to_string()))];
        while let Some((block, of)) = work.pop() {
            if chains.contains_key(&block) || block.0 >= self.blocks.len() {
                continue;
            }
            chains.insert(block, of.clone());
            for target in Self::targets(&self.blocks[block.0].instructions) {
                let theirs = versions.get(&target).cloned().unwrap_or_else(|| of.clone());
                work.push((target, theirs));
            }
        }
        chains
    }

    /// `ids` as a comma separated list, for traces.
    fn ids(ids: impl Iterator<Item = usize>) -> String {
        ids.map(|id| id.to_string()).collect::<Vec<_>>().join(",")
    }

    /// The source line of the function being specialized, for traces.
    #[cfg(feature = "tracing")]
    fn traced_line(&self, owner: &Owner) -> u64 {
        Vm::info(self.proto).1 as u64
    }

    /// `version`'s choice, for the trace (`spec`/`version`, see
    /// `tools/trace_sql.py`): with how many versions `pc` has after it, and
    /// how many of the requested context's shapes the join lost.
    #[cfg(feature = "tracing")]
    fn trace_version(&self, owner: &Owner, pc: Pc, requested: &Context, block: BlockId, outcome: &str, joined: Option<&Context>) {
        let versions = self.versions_at(owner, SubPc::new(pc), requested);
        let context = requested.tostring(owner);
        let joined_context = joined.map(|j| j.tostring(owner)).unwrap_or_default();
        let shapes_dropped = joined.map_or(0, |j| {
            (0..requested.types.len()).filter(|&i| matches!(requested.types[i], CType::Shape(..)) && !matches!(j.slot(i), CType::Shape(..))).count()
        });
        let origins = requested.values.rooted().map(|(root, fact)| {
            let from = fact.origins().map(|set| owner.ro(set).iter().map(|origin| format!("{}@{}", owner.ro(origin).block.0, owner.ro(origin).offset)).collect::<Vec<_>>().join(","));
            format!("{root:?} {fact:?} <- {}", from.unwrap_or_default())
        }).collect::<Vec<_>>().join("; ");
        crate::tracing::instant("spec", "version", &[
            ("line", self.traced_line(owner).into()),
            ("pc", pc.into()),
            ("outcome", outcome.into()),
            ("block", block.0.into()),
            ("versions", versions.into()),
            ("context", context.as_str().into()),
            ("joined", joined_context.as_str().into()),
            ("shapes_dropped", shapes_dropped.into()),
            ("origins", origins.as_str().into()),
        ]);
    }

    /// Every block, for the trace (`spec`/`block_summary`, see
    /// `tools/trace_sql.py`): its function's line (0 for a block no version
    /// names, as a thunk's layout), pc, context, residuals (how many, and as
    /// `code`, as the `graph` feature's dump shows them) and, with the JIT,
    /// hotness left and whether it has code.
    #[cfg(feature = "tracing")]
    pub fn trace_blocks(&self, owner: &Owner) {
        let mut lines: HashMap<BlockId, u64, rustc_hash::FxBuildHasher> = HashMap::default();
        for (proto, versions) in &self.versions {
            let line = Vm::info(*proto).1 as u64;
            lines.extend(versions.values().map(|&block| (block, line)));
        }
        for (id, block) in self.blocks.iter().enumerate() {
            let context = block.context.as_ref().map(|c| c.tostring(owner)).unwrap_or_default();
            let ids = |id: fn(&Residual) -> Option<u64>| block.instructions.iter().filter_map(id).map(|id| id.to_string()).collect::<Vec<_>>().join(",");
            let returns = ids(|residual| match residual { Residual::Ret(_, _, _, _, _, id, _) => Some(*id as u64), _ => None });
            let returned_from = ids(|residual| match residual { Residual::ReturnedFrom(from) => Some(from & UNKNOWN_RETURN as u64), _ => None });
            let code = block.instructions.iter().map(|residual| residual.to_string()).collect::<Vec<_>>().join("; ");
            let mut args: Vec<(&str, crate::tracing::TraceValue)> = vec![
                ("block", id.into()),
                ("line", lines.get(&BlockId(id)).copied().unwrap_or(0).into()),
                ("pc", block.pc.into()),
                ("residuals", block.instructions.len().into()),
                ("code", code.as_str().into()),
                ("context", context.as_str().into()),
                ("returns", returns.as_str().into()),
                ("returned_from", returned_from.as_str().into()),
                ("unreachable", (self.unreachable.contains(&BlockId(id)) as u64).into()),
            ];
            #[cfg(feature = "jit")]
            {
                args.push(("hotness", block.jit_info.hotness.get().into()));
                args.push(("jit_entry", (block.jit_info.entry.is_some() as u64).into()));
                args.push(("compiled", (self.jctx.blocks.contains_key(&BlockId(id)) as u64).into()));
            }
            crate::tracing::instant("spec", "block_summary", &args);
        }
    }

    /// Return a specialized block for a given PC and context, compiling a new one if necessary
    pub fn find(&mut self, owner: &mut Owner, pc: SubPc, ctx: &Rc<Context>) -> Option<BlockId>
    {
        self.versions.get(&self.proto).unwrap().get(&(pc, ctx.clone())).cloned()
    }

    pub fn compile(&mut self, owner: &mut Owner, pc: Pc, ctx: Rc<Context>, block_id: BlockId) -> Rc<Context> {
        self.compile_holding(owner, pc, ctx, block_id, Default::default())
    }

    /// `compile`, the peephole holding `held`. See Note [Peephole fusion] in `peephole`.
    fn compile_holding(&mut self, owner: &mut Owner, pc: Pc, ctx: Rc<Context>, block_id: BlockId, held: crate::peephole::Spells) -> Rc<Context> {
        // The instruction compiling this, if any, goes on after it.
        let outer = self.instruction.take();
        let ctx = self.compile_instructions(owner, pc, ctx, block_id, held);
        self.instruction = outer;
        ctx
    }

    /// Make the frames of the inlined calls code in `ctx` is in that aren't, ending `block`: the
    /// block the code goes on in, from `pc`, inside them, and its context. See Note [Peephole
    /// fusion] in `peephole`.
    fn make_frames(&mut self, block: BlockId, pc: Pc, ctx: &Context) -> (BlockId, Rc<Context>) {
        let mut made = ctx.clone();
        self.end_block(block);
        let moved: usize = made.inline.iter().filter(|frame| frame.made == Made::Base).map(InlineFrame::by).sum();
        if moved > 0 {
            self.blocks[block.0].instructions.push(Residual::Leave(moved as u16));
        }
        for frame in made.inline.iter_mut().filter(|frame| frame.made != Made::Yes) {
            self.blocks[block.0].instructions.push(frame.push());
            frame.made = Made::Yes;
        }
        let inside = self.new_block(pc);
        self.blocks[inside.0].cells = made.filled_cells();
        self.blocks[inside.0].promoted = made.promoted.clone();
        self.blocks[block.0].instructions.push(Residual::Jump(inside));
        (inside, Rc::new(made))
    }

    /// Compile on in `block` from where compiling an instruction went on to, if it went on there.
    fn go_on(&mut self, owner: &mut Owner, compiled: Compiled, block: BlockId) {
        if let Some((next, ctx, _, held)) = compiled {
            self.compile_holding(owner, next, ctx, block, held);
        }
    }

    fn compile_instructions(&mut self, owner: &mut Owner, mut pc: Pc, mut ctx: Rc<Context>, block_id: BlockId, mut carry: crate::peephole::Spells) -> Rc<Context> {
        debug_assert_eq!(ctx.types.len(), unsafe { (*self.proto).max_stack } as usize, "a context of another function's frame");
        loop {
            let inst = unsafe { self.proto.as_ref().unwrap().instructions.items[pc].clone() };
            // Only a call uses the top the instruction before left. See Note [Known top].
            if ctx.top.is_some() && !matches!(inst.0.Opcode(), Opcode::CALL | Opcode::TAILCALL) {
                Rc::make_mut(&mut ctx).top = None;
            }
            debug!("compile {pc} {:?} {:?}", inst.0.Opcode(), ctx);
            let holds = self.unheld.take() != Some(pc);
            self.instruction = Some((pc, Restart::Start(ctx.clone()), holds));
            self.entering = true;
            // An inlined call's return whose frame isn't made: the caller's code after the call goes
            // on here, the base moved back if it was moved, the results the peephole holds held in
            // the call's slots and the rest moved there. See Note [Peephole fusion] in `peephole`.
            let folds = match ctx.inline.last() {
                Some(frame) if inst.0.Opcode() == Opcode::RETURN && frame.made != Made::Yes => {
                    let (a, b) = crate::vm::AB::unpack(inst.0);
                    let (a, b) = (a as usize, b as usize);
                    // SAFETY: an inlined call's continuation lives as long as the code.
                    let continuation = unsafe { &*frame.continuation };
                    let (call, c) = (continuation.a as usize, continuation.c as usize);
                    let results = a..a + c.saturating_sub(1);
                    // Of no instruction of the caller's.
                    let spells = carry.renamed(|slot| call + slot - a, |slot| call + 1 + slot, |slot| results.contains(&slot), usize::MAX);
                    let moves: Vec<(usize, usize)> = results.clone().filter(|&slot| !carry.spells.iter().any(|spell| spell.dest == slot)).map(|slot| (call + 1 + slot, call + slot - a)).collect();
                    match continuation.rest {
                        Rest::Next(next) if b != 0 && c != 0 && c <= b && frame.b != 0 && !moves.iter().any(|&(_, to)| spells.names(to)) => Some((frame.clone(), a, b, next, spells, moves)),
                        _ => None,
                    }
                },
                _ => None,
            };
            if let Some((frame, a, b, next, spells, moves)) = folds {
                let continuation = unsafe { &*frame.continuation };
                let moved = frame.made == Made::Base;
                let by = frame.by();
                let (known, effects) = self.returned_context(owner, &ctx, continuation, a, b);
                self.end_block(block_id);
                if moved {
                    self.blocks[block_id.0].instructions.push(Residual::Leave(by as u16));
                }
                // A result in a slot still unset is nil; the frame's other unset slots are its
                // caller's temporaries, never read before written.
                let mut spells = spells;
                let unset = std::mem::take(&mut spells.unset);
                for (from, to) in moves {
                    let result: Rc<dyn Window> = if unset.contains(&from) {
                        Rc::new(crate::generators::LoadNil::new(&[to]))
                    } else {
                        Rc::new(crate::generators::Move::new(&[from, to]))
                    };
                    self.blocks[block_id.0].instructions.push(Residual::ExecWindow(result));
                }
                let callee = self.proto;
                self.set_current(continuation.proto as LProto<'_, '_>);
                self.join_effects(owner, effects);
                let after = self.new_block(next);
                self.blocks[after.0].cells = known.filled_cells();
                self.blocks[after.0].promoted = known.promoted.clone();
                self.blocks[block_id.0].instructions.push(Residual::Jump(after));
                self.entering = true;
                // The stores held named by the caller's locals where they name its temporaries.
                let mut spells = spells;
                let live = unsafe { self.proto.as_ref().unwrap() }.locals_in_scope(next).unwrap_or(usize::MAX);
                rehome(&mut spells, &known, |slot| slot >= live);
                self.compile_holding(owner, next, Rc::new(known), after, spells);
                self.set_current(callee);
                return ctx;
            }
            // A frame never entered is made nil past its arguments: nothing of it is unset.
            if matches!(inst.0.Opcode(), Opcode::TAILCALL | Opcode::RETURN) && ctx.inline.last().is_some_and(|frame| frame.made == Made::No) {
                carry.unset.clear();
            }
            // What the peephole holds, laid out before what lays out code here, as if from before
            // the instruction, going on to it. See Note [Peephole fusion] in `peephole`.
            if matches!(inst.0.Opcode(), Opcode::TAILCALL | Opcode::RETURN) && !carry.is_empty() {
                let held = std::mem::take(&mut carry);
                match self.compile_one(owner, SubPc::new(pc - 1), ctx.clone(), Gen::holding(held, emit_lay_out()), ResumeArg::Start, block_id) {
                    Some((_, laid, _, _)) => ctx = laid,
                    None => return ctx,
                }
                self.entering = true;
            }
            // Any other return of an inlined call: from its frame, made. See Note [Inlined calls].
            if matches!(inst.0.Opcode(), Opcode::TAILCALL | Opcode::RETURN) && ctx.inline.iter().any(|frame| frame.made != Made::Yes) {
                let (inside, made) = self.make_frames(block_id, pc, &ctx);
                self.entering = true;
                return self.compile_holding(owner, pc, made, inside, Default::default());
            }
            let decoded = self.decode(pc, &inst);
            if let Some((next, nctx, ret, held)) = match inst.0.Opcode() {
                _ if let Some(generator) = decoded => {
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Gen::holding_of(std::mem::take(&mut carry), generator), ResumeArg::Start, block_id)
                },
                Opcode::TAILCALL => {
                    let (a, b) = crate::vm::AB::unpack(inst.0);
                    self.end_block(block_id);
                    let proto = self.proto;
                    let closes = !captured_slots(unsafe { &*proto }).is_empty();
                    let vararg = unsafe { (*proto).is_vararg != 0 };
                    let effects: *const Cell<Effects> = self.effects_of(proto);
                    // See Note [Tail calls].
                    let site = TailSite { calling: ctx.clone(), pc, a: a as usize, b: b as usize, closes, vararg, effects };
                    let thunk = self.make_tail_call_thunk(block_id, Rc::new(site), 0, true);
                    self.blocks[block_id.0].instructions.push(Residual::Thunk(thunk)); None
                },
                Opcode::RETURN => {
                    let (a, b) = crate::vm::AB::unpack(inst.0);
                    self.end_block(block_id);
                    let proto = unsafe { &*self.proto };
                    let closes = !captured_slots(proto).is_empty();
                    // What it returns, for the continuations of the calls it returns to. Of the
                    // callee's frame, a table's shape means nothing to them. See Note [Call
                    // continuations].
                    let returns = match b {
                        0 => UNKNOWN_RETURN,
                        b => {
                            let results = (a as usize..a as usize + b as usize - 1).map(|slot| match ctx.slot(slot) {
                                CType::Shape(of, _) => CType::Type(of),
                                ctype => ctype,
                            });
                            self.return_id(results.collect())
                        },
                    };
                    let effects: *const Cell<Effects> = self.effects_of(proto);
                    // An inlined callee's returns to the code after its call. See Note [Inlined calls].
                    if !ctx.inline.is_empty() {
                        let thunk = self.make_inline_return_thunk(block_id, ctx.clone(), a as usize, b, closes);
                        self.blocks[block_id.0].instructions.push(Residual::Thunk(thunk));
                    } else {
                        self.blocks[block_id.0].instructions.push(Residual::Ret(pc, a, b, closes, proto.is_vararg != 0, returns, effects));
                    }
                    None
                },
                x => {
                    #[cfg(debug_assertions)]
                    {
                        unreachable!("{:?}", x)
                    }
                    panic!("{:?}", x);
                    let proto = self.proto;
                    let vararg = unsafe { (*proto).is_vararg != 0 };
                    let effects: *const Cell<Effects> = self.effects_of(proto);
                    self.blocks[block_id.0].instructions.push(Residual::Ret(pc, 0, 0, true, vararg, UNKNOWN_RETURN, effects)); None
                },
            } {
                self.entering = false;
                pc = next;
                ctx = nctx;
                carry = held;
                debug!("-> {}", next);
            } else {
                self.entering = false;
                debug_assert!(carry.is_empty(), "a block ended holding integer ops");
                return ctx;
            }
        }
    }

    /// The generator of instruction `inst` at `pc`, compiled as a coroutine run in the peephole, if
    /// it is: all but what the specializer lays out itself. See Note [Peephole fusion] in
    /// `peephole`.
    fn decode(&self, pc: Pc, inst: &crate::chunk::Instruction) -> Option<Box<dyn NativeGen>> {
        match inst.0.Opcode() {
            op @ (Opcode::ADD | Opcode::SUB | Opcode::MUL | Opcode::DIV | Opcode::MOD | Opcode::POW) => {
                let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                debug!("{a} {b} {c}");
                Some(Box::new(emit_numeric(op, a as usize, b as usize, c as usize)))
            },
            op @ (Opcode::EQ | Opcode::LT | Opcode::LE) => {
                let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                debug!("{a} {b} {c}");
                Some(Box::new(emit_compare(op, a, b as usize, c as usize, pc + 1)))
            },
            Opcode::TEST => {
                let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                Some(Box::new(emit_test(a as usize, c, pc + 1)))
            },
            Opcode::TESTSET => {
                let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                Some(Box::new(emit_testset(a as usize, b as usize, c, pc + 1)))
            },
            Opcode::NOT => {
                let (a, b) = crate::vm::AB::unpack(inst.0);
                Some(Box::new(emit_not(a as usize, b as usize)))
            },
            Opcode::CLOSE => {
                let (a, _) = crate::vm::AB::unpack(inst.0);
                Some(Box::new(emit_close(a as usize)))
            },
            Opcode::TFORLOOP => {
                let (a, _, c) = crate::vm::ABC::unpack(inst.0);
                Some(Box::new(emit_tforloop(a as usize, c as usize, pc + 1)))
            },
            Opcode::VARARG => {
                let (a, b) = crate::vm::AB::unpack(inst.0);
                let params = unsafe { (*self.proto).param_count as usize };
                Some(Box::new(emit_vararg(a as usize, b as usize, params)))
            },
            Opcode::JMP => {
                let sbx = crate::vm::sBx::unpack(inst.0);
                Some(Box::new(emit_jmp(sbx, pc + 1)))
                //self.blocks[block_id].push(Residual::Jump(((pc as isize) + sbx as isize) as usize)); return ctx;
            },
            Opcode::UNM => {
                let (a, b) = crate::vm::AB::unpack(inst.0);
                Some(Box::new(emit_unm(a as usize, b as usize)))
            },
            Opcode::LEN => {
                let (a, b) = crate::vm::AB::unpack(inst.0);
                Some(Box::new(emit_len(a as usize, b as usize)))
            },
            Opcode::CONCAT => {
                let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                Some(Box::new(emit_concat(a as usize, b as usize, c as usize)))
            },
            Opcode::LOADK => {
                let (a, bx) = crate::vm::ABx::unpack(inst.0);
                let c: LValue<'src, 'intern> = unsafe { (&(&(*self.proto).constants.items)[bx as usize]).into() };
                Some(Box::new(emit_loadk(bx, c.typeof_(), a as usize)))
            },
            Opcode::LOADNIL => {
                let (a, b) = crate::vm::AB::unpack(inst.0);
                Some(Box::new(emit_loadnil(a as usize, b as usize)))
            },
            Opcode::LOADBOOL => {
                let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                Some(Box::new(emit_loadbool(a as usize, b != 0, c != 0, pc + 1)))
            },
            Opcode::MOVE => {
                let (a, b) = crate::vm::AB::unpack(inst.0);
                debug!("move {} {}", a, b);
                Some(Box::new(emit_move(a as usize, b as usize)))
            },
            Opcode::FORPREP => {
                let (a, sbx) = crate::vm::AsBx::unpack(inst.0);
                Some(Box::new(emit_forprep(a as usize, sbx, pc + 1)))
            },
            Opcode::FORLOOP => {
                let (a, sbx) = crate::vm::AsBx::unpack(inst.0);
                Some(Box::new(emit_forloop(a as usize, sbx, pc + 1)))
            },
            Opcode::GETUPVAL => {
                let (a, b) = crate::vm::AB::unpack(inst.0);
                Some(Box::new(emit_getupval(a as usize, b as usize)))
            },
            Opcode::SETUPVAL => {
                let (a, b) = crate::vm::AB::unpack(inst.0);
                Some(Box::new(emit_setupval(a as usize, b as usize)))
            },
            Opcode::CLOSURE => {
                let (a, bx) = crate::vm::ABx::unpack(inst.0);
                let proto = unsafe { &*self.proto };
                let count = proto.prototypes.items[bx as usize].upval_count as usize;
                let upvalues = proto.instructions.items[pc + 1..pc + 1 + count].iter()
                    .map(|pseudo| (pseudo.0.Opcode(), crate::vm::AB::unpack(pseudo.0).1 as usize))
                    .collect();
                Some(Box::new(emit_closure(a as usize, bx as usize, upvalues, pc + 1 + count)))
            },
            Opcode::SELF => {
                let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                Some(Box::new(emit_self(a as usize, b as usize, c as usize)))
            },
            Opcode::CALL => {
                let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                debug!("{} {} {}", a, b, c);
                // TODO: this should try to compile a new block and jump to it, and only
                // fallback to a trace exit if we need to run the fully generic code
                Some(Box::new(emit_call(a as usize, b as usize, c as usize)))
            },
            Opcode::GETGLOBAL => {
                let (a, bx) = crate::vm::ABx::unpack(inst.0);
                let kst = unsafe { &(&(*self.proto).constants.items)[bx as usize] };
                debug!("getglobal {} {} {:?}", a, bx, &kst);
                Some(Box::new(emit_getglobal(a as usize, bx as usize)))
            },
            Opcode::SETGLOBAL => {
                let (a, bx) = crate::vm::ABx::unpack(inst.0);
                let kst = unsafe { &(&(*self.proto).constants.items)[bx as usize] };
                Some(Box::new(emit_setglobal(a as usize, bx as usize)))
            },
            Opcode::GETTABLE => {
                let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                debug!("gettable {} {} {}", a, b, c);
                Some(Box::new(emit_gettable(a as usize, b as usize, c as usize)))
            },
            Opcode::SETTABLE => {
                let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                debug!("settable {} {} {}", a, b, c);
                Some(Box::new(emit_settable(a as usize, b as usize, c as usize)))
            },
            Opcode::NEWTABLE => {
                let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                Some(Box::new(emit_newtable(a as usize, b as usize, c as usize)))
            },
            Opcode::SETLIST => {
                let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                Some(Box::new(emit_setlist(a as usize, b as usize, c as usize)))
            },
            _ => None,
        }
    }

    /// Where a jump in `ctx` to `target` goes: `target`, a version of a pc whose
    /// context accepts the jump's, once it forgets the types of registers
    /// holding no local (`forgotten`). See Note [Version compatibility].
    fn edge(&mut self, owner: &mut Owner, ctx: &Context, target: BlockId) -> BlockId {
        let Some(entered) = self.blocks[target.0].context.clone() else { return target };
        let pc = self.blocks[target.0].pc;
        let live = unsafe { self.proto.as_ref().unwrap() }.locals_in_scope(pc).unwrap_or(usize::MAX);
        let mut jumping = ctx.clone();
        forget_dead(owner, &mut jumping, live, None);
        // A jump may keep a register it wrote (`GetBlockKeeping`).
        assert!(entered.accepts(&jumping) || entered.accepts(ctx), "a jump in {} to a version for {}", jumping.tostring(owner), entered.tostring(owner));
        target
    }

    /// Before the residual ending a block: its GC safepoint, if it may have
    /// allocated since its last. See Note [Block safepoints].
    fn end_block(&mut self, block_id: BlockId) {
        let block = &mut self.blocks[block_id.0];
        if std::mem::take(&mut block.allocates) {
            block.instructions.push(Residual::GC);
        }
    }

    /// The context a jump in `ctx` to `dest_pc` carries: it forgets the types of
    /// every register not holding a local in scope there (`forgotten`), and the
    /// fragile facts about them, and which array a value of known type was
    /// loaded from, which lets paths that differ only in them share the target's
    /// version. See Note [Jumped-to contexts].
    fn jumping(&self, owner: &mut Owner, ctx: Rc<Context>, dest_pc: Pc) -> Rc<Context> {
        self.jumping_keeping(owner, ctx, dest_pc, None)
    }

    /// `jumping`, keeping what is known of register `kept`, which the jumping instruction wrote.
    /// See Note [Jumped-to contexts].
    fn jumping_keeping(&self, owner: &mut Owner, mut ctx: Rc<Context>, dest_pc: Pc, kept: Option<usize>) -> Rc<Context> {
        let in_scope = unsafe { self.proto.as_ref().unwrap() }.locals_in_scope(dest_pc);
        if let Some(in_scope) = in_scope.filter(|&in_scope| forgets(&ctx, in_scope)) {
            forget_dead(owner, Rc::make_mut(&mut ctx), in_scope, kept);
        }
        // An element of a known type was guarded, or its array's kind is known:
        // what it was loaded from tells no more. Only the version jumped to is
        // found without it, so it still accepts the jump. See Note [Array kinds].
        let typed: Vec<usize> = (0..ctx.types.len())
            .filter(|&slot| ctx.slot(slot) != CType::Unknown && ctx.values.has_field(Loc::root(Root::Slot(slot as u16)), Label::ElementOf))
            .collect();
        if !typed.is_empty() {
            let known = Rc::make_mut(&mut ctx);
            for slot in typed {
                known.values.unlink(Loc::root(Root::Slot(slot as u16)), Label::ElementOf);
            }
        }
        ctx
    }

    /// A new, empty block starting at `pc` (see `Block::pc`).
    pub fn new_block(&mut self, pc: Pc) -> BlockId {
        self.blocks.push(Block { proto: self.proto as usize, ..Block::new(pc) });
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
    /// What the peephole holds, `held`, stays held on both its ways. See Note [Peephole fusion] in
    /// `peephole`.
    fn make_dynamic_thunk(&self, block_id: BlockId, thunk_coro: Box<Gen>, test: Rc<dyn Window>, pc: SubPc, thunk_ctx: Rc<Context>) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            test.interp(owner, state);
            let passed = state.select == 1;
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

    /// Whether the promote at `site` of the running function has, or may have, a version for
    /// `value`: one of the first `PROMOTE_SITE_VALUES` values it sees. See Note [Promoted values].
    fn promotes(&mut self, site: Pc, value: i32) -> bool {
        let values = self.promoted.entry((self.proto, site)).or_default();
        values.contains(&value) || (values.len() < PROMOTE_SITE_VALUES && values.insert(value))
    }

    /// The thunk a `Promote` of `slot` ends its block in: forced, it guards the
    /// slot equal to the integer it holds, and continues past the guard with
    /// that value promoted, the guard's other way promoting again. See Note [Promoted values].
    fn make_promote_thunk(&self, block_id: BlockId, thunk_coro: Box<Gen>, slot: usize, pc: SubPc, thunk_ctx: Rc<Context>) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            let LValue::Integer(value) = state.vals[state.base + slot].unbox() else { unreachable!("a promote's argument is an integer") };
            if !vm.promotes(pc.0, value) {
                let rest = vm.subblock(owner, pc.next_false(), thunk_ctx.clone(), thunk_coro.clone(), ResumeArg::Failed);
                vm.jump_thunk(block_id, thunk_pc, rest);
                return;
            }
            let test: Rc<dyn Window> = Rc::new(crate::generators::EqualsK::new(value, &[slot]));
            // In place, unless the thunk's JIT code can only be patched to a jump.
            // See Note [Thunk patching].
            let block = if vm.compiled(block_id) {
                let guard_block = vm.new_block(pc.0);
                vm.jump_thunk(block_id, thunk_pc, guard_block);
                vm.blocks[guard_block.0].instructions.push(Residual::GuardDynamic(test));
                guard_block
            } else {
                vm.blocks[block_id.0].instructions[thunk_pc] = Residual::GuardDynamic(test);
                block_id
            };
            // Past the guard, the slot holds the value too.
            let mut promoted = thunk_ctx.clone();
            Rc::make_mut(&mut promoted).promote(pc.0, value);
            Rc::make_mut(&mut promoted).values.learn(Loc::root(Root::Slot(slot as u16)), Known::Constant { value, origins: None });
            let pass = vm.subblock(owner, pc.next_true(), promoted, thunk_coro.clone(), ResumeArg::Integer(value));
            let fail = vm.make_side_thunk(block, thunk_coro.clone(), pc.next_false(), thunk_ctx.clone(), ResumeArg::Failed);
            vm.blocks[block.0].instructions.push(Residual::Thunk(fail));
            vm.blocks[block.0].instructions.push(Residual::Jump(pass));
        })))
    }

    /// A `GuardDynamic`'s side not yet taken, compiled and jumped to in its
    /// place when first taken. See Note [Dynamic guards].
    /// The thunk a `Narrow` of `slot`, a double, ends its block in. See Note
    /// [Narrowing].
    fn make_narrow_thunk(&self, block_id: BlockId, thunk_coro: Box<Gen>, slot: usize, pc: SubPc, thunk_ctx: Rc<Context>) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            let value = state.vals[state.base + slot];
            let whole = value.representation() == LType::Double && value.as_number().is_some_and(crate::lboxed::is_integer);
            if !whole {
                // Not narrowed, so not tried at runtime.
                let rest = vm.subblock(owner, pc.next_false(), thunk_ctx.clone(), thunk_coro.clone(), ResumeArg::Failed);
                vm.jump_thunk(block_id, thunk_pc, rest);
                return;
            }
            // Narrowed by an optimistic op: on its hot path the slot is an integer, on
            // its cold path still the double. See Note [Optimistic ops].
            let at = vm.new_block(pc.0);
            vm.jump_thunk(block_id, thunk_pc, at);
            let mut written = thunk_ctx.clone();
            Rc::make_mut(&mut written).effect(Effect::Write(slot));
            let mut narrowed = written.clone();
            Rc::make_mut(&mut narrowed).set_types(owner, vec![(slot, CType::Type(LType::Integer))]);
            vm.blocks[at.0].instructions.push(Residual::ExecWindow(Rc::new(crate::generators::ToInteger::new(&[slot]))));
            let hot = vm.subblock(owner, pc.next_true(), narrowed, thunk_coro.clone(), ResumeArg::Matched);
            let cold = vm.new_block(pc.0);
            let side = vm.make_side_thunk(cold, thunk_coro.clone(), pc.next_false(), written, ResumeArg::Failed);
            vm.blocks[cold.0].instructions.push(Residual::Thunk(side));
            vm.blocks[at.0].instructions.push(Residual::Branch { hot, cold });
        })))
    }

    /// Widen slot `slot` of `block`, an integer, statically if a fact says it holds a
    /// whole constant: the constant is stored again in the double encoding, and its
    /// load queued to be rebuilt as a double. Whether it was. See Note [Widening].
    fn widen_constant(&mut self, owner: &mut Owner, ctx: &mut Rc<Context>, slot: usize, block: BlockId) -> bool {
        let Some(value) = ctx.constant(slot) else { return false };
        // Rebuilt from where the constant was loaded, as a double. See Note
        // [Contraction].
        if let Some(set) = ctx.values.fact(Loc::root(Root::Slot(slot as u16)), CONSTANT).and_then(Known::origins) {
            let origins: Vec<Origin> = owner.ro(set).iter().filter(|origin| owner.ro(origin).rebuild.is_some()).cloned().collect();
            let queued = |origin: &Origin| self.contractions.iter().any(|(_, queued, _)| queued.iter().any(|known| Rc::ptr_eq(known, origin)));
            let queues = !origins.is_empty() && !origins.iter().all(queued);
            #[cfg(feature = "tracing")]
            crate::tracing::instant("spec", "widen", &[
                ("line", self.traced_line(owner).into()),
                ("slot", slot.into()),
                ("block", block.0.into()),
                ("origins", owner.ro(set).iter().map(|origin| {
                    let o = owner.ro(origin);
                    format!("{}@{}{}", o.block.0, o.offset, if o.rebuild.is_some() { "" } else { " rebuilt" })
                }).collect::<Vec<_>>().join(",").as_str().into()),
                ("queued", (queues as u64).into()),
            ]);
            if queues {
                self.contractions.push((self.proto, origins, ResumeArg::Type(CType::Type(LType::Double))));
            }
        }
        self.blocks[block.0].instructions.push(Residual::ExecWindow(Rc::new(crate::generators::WidenK::new(value, &[slot]))));
        // The fact dropped by the write: its type says what it would, so no version
        // keeps it apart.
        let ctx = Rc::make_mut(ctx);
        ctx.effect(Effect::Write(slot));
        ctx.set_types(owner, vec![(slot, CType::Type(LType::Double))]);
        true
    }

    /// Where the yield of `coro` at `pc` in `ctx` introduces a fact: rebuilding
    /// truncates `block` there and resumes `coro` in `ctx`, without the fact.
    /// See Note [Contraction].
    fn origin(&self, block: BlockId, coro: Box<Gen>, pc: SubPc, ctx: Rc<Context>) -> Origin {
        let offset = self.blocks[block.0].instructions.len();
        // Its function's, which needn't be the frame's it runs in: an inlined call's frame the
        // peephole holds isn't made. See Note [Peephole fusion] in `peephole`.
        let proto = self.proto as LProto<'static, 'static>;
        // The origin becomes a thunk laying out the rebuilt code. See Note [Contraction].
        let rebuild = move |vm: &mut Specializer, owner: &mut Owner, how: ResumeArg| {
            let thunk = ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
                // In place, unless the thunk's JIT code can only be patched to a jump (Note [Thunk
                // patching] in `jit`). Nothing returns into the residuals after it, which it
                // truncates: the rebuild waited until nothing ran past it.
                assert!(!state.callstack.iter().filter_map(|entry| entry.returns_to()).any(|ret| ret.0 == block && ret.1 > thunk_pc), "a frame returns past a rebuilt origin");
                let at = if vm.compiled(block) {
                    let at = vm.new_block(pc.0);
                    vm.jump_thunk(block, thunk_pc, at);
                    at
                } else {
                    vm.blocks[block.0].instructions.truncate(thunk_pc);
                    if vm.cuts.get(&block).is_some_and(|&cut| cut > thunk_pc) {
                        vm.cuts.remove(&block);
                    }
                    block
                };
                vm.rebuilding.remove(&(block, offset));
                let running = vm.proto;
                vm.set_current(proto as LProto<'_, '_>);
                let compiled = vm.compile_one(owner, pc, ctx.clone(), coro.clone(), how.clone(), at);
                vm.go_on(owner, compiled, at);
                vm.set_current(running);
            })));
            // The earliest's of the origins sharing the residual. See Note [Contraction].
            if vm.rebuilding.get(&(block, offset)).is_some_and(|&earlier| earlier < pc.0) {
                return;
            }
            vm.rebuilding.insert((block, offset), pc.0);
            let residuals = &mut vm.blocks[block.0].instructions;
            if offset < residuals.len() {
                residuals[offset] = Residual::Thunk(thunk);
            } else {
                residuals.push(Residual::Thunk(thunk));
            }
            vm.cuts.insert(block, offset + 1);
        };
        Rc::new(TLCell::new(OriginState { rebuild: Some(Box::new(rebuild)), block, offset, pc, used: false }))
    }

    /// The thunk an optimistic integer op's `Encoding` ends its block in: forced, it lays out the
    /// op as the integer one, from an origin its first overflow rebuilds it from, if its result
    /// fits for its operands' values, and else as the double one. See Note [Optimistic ops].
    fn make_encoding_thunk(&self, block_id: BlockId, thunk_coro: Box<Gen>, pc: SubPc, thunk_ctx: Rc<Context>, fits: Fits) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            // In place, unless the thunk's JIT code can only be patched to a jump. See Note
            // [Thunk patching].
            let at = if vm.compiled(block_id) {
                let at = vm.new_block(pc.0);
                vm.jump_thunk(block_id, thunk_pc, at);
                at
            } else {
                vm.blocks[block_id.0].instructions.truncate(thunk_pc);
                block_id
            };
            let fit = (fits.0)(state);
            #[cfg(feature = "tracing")]
            crate::tracing::instant("spec", "encoding", &[
                ("line", vm.traced_line(owner).into()),
                ("pc", pc.0.into()),
                ("block", at.0.into()),
                ("encoding", if fit { "integer" } else { "double" }.into()),
            ]);
            let answer = if fit {
                vm.encoding = Some(vm.origin(at, thunk_coro.clone(), pc, thunk_ctx.clone()));
                ResumeArg::Type(CType::Type(LType::Integer))
            } else {
                ResumeArg::Type(CType::Type(LType::Double))
            };
            let compiled = vm.compile_one(owner, pc, thunk_ctx.clone(), thunk_coro.clone(), answer, at);
            vm.go_on(owner, compiled, at);
            vm.encoding = None;
        })))
    }

    /// An optimistic op's cold way, as `make_side_thunk`'s, which the first time it's taken also
    /// queues where the op's encoding was asked, if anywhere, to be rebuilt computing it in the
    /// double encoding. See Note [Optimistic ops].
    fn make_overflow_thunk(&self, block_id: BlockId, thunk_coro: Box<Gen>, pc: SubPc, thunk_ctx: Rc<Context>, asked: Option<Origin>) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            let side = vm.subblock(owner, pc, thunk_ctx.clone(), thunk_coro.clone(), ResumeArg::Failed);
            vm.jump_thunk(block_id, thunk_pc, side);
            if !overflow_rebuilds() {
                return;
            }
            let Some(origin) = asked.clone().filter(|origin| owner.ro(origin).rebuild.is_some()) else { return };
            let queued = vm.contractions.iter().any(|(_, queued, _)| queued.iter().any(|known| Rc::ptr_eq(known, &origin)));
            if !queued {
                vm.contractions.push((vm.proto, vec![origin], ResumeArg::Type(CType::Type(LType::Double))));
            }
        })))
    }

    /// The exit a held spell failing takes, from `block`: it writes `materialize`, the spells not
    /// yet written, as their operations would, and goes on from `restart`, in instruction `at`,
    /// with slots `unknown` unknown, the instruction's integer op not held. Never another
    /// version's, which might hold it. See Note [Peephole fusion] in `peephole`.
    fn make_held_exit(&self, block: BlockId, materialize: Vec<Rc<dyn Window>>, unknown: Vec<usize>, at: Pc, restart: Restart) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            let exit = vm.new_block(at);
            for window in &materialize {
                vm.blocks[exit.0].instructions.push(Residual::ExecWindow(window.clone()));
            }
            let unknowing = |owner: &mut Owner, mut ctx: Rc<Context>| {
                let ctx_mut = Rc::make_mut(&mut ctx);
                ctx_mut.set_types(owner, unknown.iter().map(|&slot| (slot, CType::Unknown)).collect());
                for &slot in &unknown {
                    ctx_mut.effect(Effect::Write(slot));
                }
                ctx
            };
            vm.unheld = Some(at);
            match &restart {
                Restart::Start(start) => {
                    let ctx = unknowing(owner, start.clone());
                    vm.compile(owner, at, ctx, exit);
                },
                Restart::Resume(pc, ctx, coro, arg) => {
                    let ctx = unknowing(owner, ctx.clone());
                    let compiled = vm.compile_one(owner, *pc, ctx, coro.forgetting(), arg.clone(), exit);
                    vm.go_on(owner, compiled, exit);
                },
            }
            vm.jump_thunk(block, thunk_pc, exit);
        })))
    }

    /// The thunk a `Learn` of `slot` ends its block in: forced, the code after it with the string
    /// keys of the table there then, in order. See `jit.learn` in `library`.
    fn make_learn_thunk(&self, block_id: BlockId, thunk_coro: Box<Gen>, slot: usize, pc: SubPc, thunk_ctx: Rc<Context>) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            let LValue::Table(tab) = state.vals[state.base + slot].unbox() else { unreachable!("jit.learn of a table") };
            let mut keys: Vec<LConstant<'static, 'static>> = tab.ro(owner).hash.keys().filter_map(|key| match key.boxed().unbox() {
                // As the generator's constants, the intern arena outlives the code.
                LValue::InternedString(name) => Some(unsafe { core::mem::transmute::<LConstant<'_, '_>, LConstant<'static, 'static>>(crate::chunk::Constant::String(name)) }),
                _ => None,
            }).collect();
            keys.sort_by(|a, b| match (a, b) {
                (crate::chunk::Constant::String(a), crate::chunk::Constant::String(b)) => a.as_bytes().cmp(b.as_bytes()),
                _ => std::cmp::Ordering::Equal,
            });
            let rest = vm.subblock(owner, pc.next_true(), thunk_ctx.clone(), thunk_coro.clone(), ResumeArg::Keys(keys.into()));
            vm.jump_thunk(block_id, thunk_pc, rest);
        })))
    }

    /// The thunk a `LearnKind` of `slot` ends its block in: forced on a table whose array part is of
    /// one kind, a guard of it, past which the context knows it; else the code after it, knowing
    /// nothing more. See `jit.learn` in `library`.
    fn make_learn_kind_thunk(&self, block_id: BlockId, thunk_coro: Box<Gen>, slot: usize, pc: SubPc, thunk_ctx: Rc<Context>) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            let LValue::Table(tab) = state.vals[state.base + slot].unbox() else { unreachable!("jit.learn of a table's field") };
            let kind = tab.ro(owner).kind;
            const TYPES: [LType; 8] = [LType::Nil, LType::Bool, LType::String, LType::Closure, LType::Table, LType::Integer, LType::Double, LType::Userdata];
            let Some(of) = TYPES.into_iter().find(|t| t.bit() == kind).filter(|&t| t != LType::Nil) else {
                let rest = vm.subblock(owner, pc.next_false(), thunk_ctx.clone(), thunk_coro.clone(), ResumeArg::Failed);
                vm.jump_thunk(block_id, thunk_pc, rest);
                return;
            };
            let test: Rc<dyn Window> = Rc::new(KindIs::new(of, &[slot]));
            // In place, unless the thunk's JIT code can only be patched to a jump. See Note
            // [Thunk patching].
            let block = if vm.compiled(block_id) {
                let guard_block = vm.new_block(pc.0);
                vm.jump_thunk(block_id, thunk_pc, guard_block);
                vm.blocks[guard_block.0].instructions.push(Residual::GuardDynamic(test));
                guard_block
            } else {
                vm.blocks[block_id.0].instructions[thunk_pc] = Residual::GuardDynamic(test);
                block_id
            };
            let mut known = (*thunk_ctx).clone();
            known.learn_kind(Root::Slot(slot as u16), Kind::Of(of));
            let pass = vm.subblock(owner, pc.next_true(), Rc::new(known), thunk_coro.clone(), ResumeArg::Matched);
            let fail = vm.make_side_thunk(block, thunk_coro.clone(), pc.next_false(), thunk_ctx.clone(), ResumeArg::Failed);
            vm.blocks[block.0].instructions.push(Residual::Thunk(fail));
            vm.blocks[block.0].instructions.push(Residual::Jump(pass));
        })))
    }

    /// Trip `tab`'s watchpoint: it is no longer watched, its watch sites are unpublished, and each
    /// frame paused at a call goes on in code knowing no element. See Note [Watched tables].
    fn trip(&mut self, owner: &mut Owner, state: &mut RunState, tab: Tc<Table>) {
        tab.rw(owner).watched = false;
        self.tripped(owner, state, tab.0.to_addr());
    }

    /// Handle the watchpoints natives' stores tripped, if any. See Note [Watched tables].
    fn trip_pending(&mut self, owner: &mut Owner, state: &mut RunState) {
        if !crate::vm::TRIPPED.swap(false, std::sync::atomic::Ordering::Relaxed) {
            return;
        }
        for table in crate::vm::PENDING_TRIPS.with(|pending| std::mem::take(&mut *pending.borrow_mut())) {
            self.tripped(owner, state, table);
        }
    }

    /// The table at `table` was tripped. See `trip`.
    fn tripped(&mut self, owner: &mut Owner, state: &mut RunState, table: u64) {
        self.frozen.retain(|_, frozen| frozen.0.to_addr() != table);
        for site in self.watches.remove(&table).unwrap_or_default() {
            let Location(block, off) = site.at;
            self.blocks[block.0].instructions[off] = Residual::Thunk(site.unwatched);
            #[cfg(feature = "jit")]
            self.unlink_thunk(block, off);
        }
        for i in 0..state.callstack.len() {
            let ret = match state.callstack[i].ret {
                Return::To(at) => match self.continuation_sites.get(&at).cloned() {
                    Some(site) if site.ctx.trips() => {
                        // The code of the function the frame runs, which needn't be the tripping one.
                        let block = self.new_block(self.blocks[at.0.0].pc);
                        self.blocks[block.0].proto = self.blocks[at.0.0].proto;
                        let mut ctx = (*site.ctx).clone();
                        ctx.effect(Effect::Trip);
                        let after = match site.after {
                            After::Version(pc, ctx) => {
                                let mut ctx = (*ctx).clone();
                                ctx.effect(Effect::Trip);
                                After::Version(pc, Rc::new(ctx))
                            },
                            after => after,
                        };
                        let thunk = self.make_continuation_thunk(block, Rc::new(ctx), site.captured, site.rest, site.a, site.c, after, None, 0, true);
                        self.blocks[block.0].instructions.push(Residual::Thunk(thunk));
                        Return::To(Location(block, 0))
                    },
                    _ => continue,
                },
                Return::Inlined(continuation) => {
                    let continuation = unsafe { &*(continuation as *const Continuation) };
                    if !continuation.caller.trips() {
                        continue;
                    }
                    let mut caller = continuation.caller.clone();
                    caller.effect(Effect::Trip);
                    let unwatched = Rc::new(Continuation { caller, ..continuation.clone() });
                    let at = Rc::as_ptr(&unwatched) as u64;
                    self.continuations.push(unwatched);
                    Return::Inlined(at)
                },
            };
            state.callstack[i].ret = ret;
        }
    }

    /// The thunk a watch site of the table in `slot` ends its block in: forced on a watched table,
    /// if `watches`, it is one of the table's watch sites, the code after it knowing the table is
    /// still watched; else, as the site a trip puts back, the code after it knowing nothing. See
    /// Note [Watched tables].
    fn make_watch_thunk(&self, block_id: BlockId, thunk_coro: Box<Gen>, slot: usize, pc: SubPc, thunk_ctx: Rc<Context>, watches: bool, freezes: bool) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            let boxed = state.vals[state.base + slot];
            let LValue::Table(tab) = boxed.unbox() else { unreachable!("a watch site of a table") };
            let site = (vm.proto as usize, pc.0);
            let watched = watches && vm.watch_versions.get(&site).is_none_or(|&versions| versions < MAX_VERSIONS) && {
                if freezes {
                    tab.rw(owner).watched = true;
                }
                tab.ro(owner).watched
            };
            if !watched {
                let rest = vm.subblock(owner, pc.next_false(), thunk_ctx.clone(), thunk_coro.clone(), ResumeArg::Failed);
                vm.jump_thunk(block_id, thunk_pc, rest);
                return;
            }
            *vm.watch_versions.entry(site).or_default() += 1;
            let unwatched = vm.make_watch_thunk(block_id, thunk_coro.clone(), slot, pc, thunk_ctx.clone(), false, false);
            vm.watches.entry(tab.0.to_addr()).or_default().push(WatchSite { at: Location(block_id, thunk_pc), unwatched });
            // SAFETY: as `ctypeof_`'s: the specializer is parameterized over the VM's own lifetimes,
            // which the thunk's signature doesn't say, and it outlives the table it roots.
            vm.frozen.insert(boxed.bits(), unsafe { core::mem::transmute::<Tc<Table<'_, '_>>, Tc<Table<'static, 'static>>>(tab.clone()) });
            // Which table it is, past a guard; another table fails it to a site of its own.
            let guard = vm.new_block(pc.0);
            vm.blocks[block_id.0].instructions[thunk_pc] = Residual::PatchableJump(guard);
            #[cfg(feature = "jit")]
            vm.link_thunk(block_id, thunk_pc, guard);
            let mut ctx = thunk_ctx.clone();
            Rc::make_mut(&mut ctx).values.learn(Loc::root(Root::Slot(slot as u16)), Known::Watched(boxed.bits()));
            let pass = vm.subblock(owner, pc.next_true(), ctx, thunk_coro.clone(), ResumeArg::Matched);
            let (coro, ctx) = (thunk_coro.clone(), thunk_ctx.clone());
            let other = ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, _: &mut Owner, _: &mut RunState, other_pc: usize| {
                let site = vm.new_block(pc.0);
                let thunk = vm.make_watch_thunk(site, coro.clone(), slot, pc, ctx.clone(), true, freezes);
                vm.blocks[site.0].instructions.push(Residual::Thunk(thunk));
                vm.jump_thunk(guard, other_pc, site);
            })));
            vm.blocks[guard.0].instructions.extend([
                Residual::GuardDynamic(Rc::new(crate::generators::IsValue::new(boxed.bits(), &[slot]))),
                Residual::Thunk(other),
                Residual::Jump(pass),
            ]);
        })))
    }

    /// The element of the table in `table` at RK `key`, as `ResumeArg::Element`, if the context
    /// knows which frozen table it is and the key, and the element is in its array part, not nil.
    /// See Note [Frozen tables].
    fn frozen_element(&self, owner: &Owner, ctx: &Context, table: usize, key: usize) -> Option<ResumeArg> {
        let Some(&Known::Watched(bits)) = ctx.values.fact(Loc::root(Root::Slot(table as u16)), WATCHED) else { return None };
        let tab = self.frozen.get(&bits)?;
        let k = if key & 0x100 != 0 {
            let crate::chunk::Constant::Number(n) = (unsafe { &(&(*self.proto).constants.items)[key & 0xff] }) else { return None };
            is_integer(n.0).then_some(n.0 as i64)?
        } else {
            ctx.constant(key)? as i64
        };
        let element = *tab.ro(owner).array.get(usize::try_from(k - 1).ok()?)?;
        if element.is_nil() {
            return None;
        }
        let value = element.unbox();
        let constant = match value {
            LValue::Integer(value) => i32::try_from(value).ok(),
            _ => None,
        };
        Some(ResumeArg::Element(element.bits(), value.ctypeof_(), constant))
    }

    fn make_side_thunk(&self, block_id: BlockId, thunk_coro: Box<Gen>, pc: SubPc, thunk_ctx: Rc<Context>, arg: ResumeArg) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            let side = vm.subblock(owner, pc, thunk_ctx.clone(), thunk_coro.clone(), arg.clone());
            vm.jump_thunk(block_id, thunk_pc, side);
        })))
    }

    /// The thunk a `Versions` ends its block in: forced, it lays out the code after with the
    /// count, at a point of its own: at the call's, the version found would be the one the
    /// thunk is in. See `jit.versions` in `library`.
    fn make_versions_thunk(&self, block_id: BlockId, thunk_coro: Box<Gen>, pc: SubPc, thunk_ctx: Rc<Context>) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            let count = vm.versions_entering(owner, block_id);
            let rest = vm.subblock(owner, pc.next_true(), thunk_ctx.clone(), thunk_coro.clone(), ResumeArg::Integer(count as i32));
            vm.jump_thunk(block_id, thunk_pc, rest);
        })))
    }

    /// The most versions the running function has at the point of a version code reaching
    /// `block` was entered at: those it has there, apart from those the trimming found
    /// unreachable and those a queued contraction will forget. See `jit.versions` in `library`.
    fn versions_entering(&self, owner: &Owner, block: BlockId) -> usize {
        let mut from: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
        for (id, at) in self.blocks.iter().enumerate() {
            for target in Self::targets(&at.instructions) {
                from.entry(target).or_default().push(BlockId(id));
            }
        }
        // Back from `block` to the versions code reaching it was entered at.
        let mut entries: Vec<BlockId> = Vec::new();
        let mut seen: std::collections::HashSet<BlockId> = std::collections::HashSet::new();
        let mut work = vec![block];
        while let Some(at) = work.pop() {
            if !seen.insert(at) {
                continue;
            }
            if self.blocks[at.0].context.is_some() {
                entries.push(at);
            } else {
                work.extend(from.get(&at).into_iter().flatten().copied());
            }
        }
        let doomed = |ctx: &Context| ctx.values.all_facts().any(|fact| fact.origins().is_some_and(|set| owner.ro(set).iter().any(|origin| {
            self.contractions.iter().any(|(of, queued, _)| *of == self.proto && queued.iter().any(|known| Rc::ptr_eq(known, origin)))
        })));
        let versions = self.versions.get(&self.proto).unwrap();
        entries.iter().filter_map(|entry| versions.iter().find(|(_, block)| **block == *entry).map(|(key, _)| key)).map(|(at, ctx)| {
            versions.iter().filter(|((there, theirs), block)| there == at && theirs.same_point(ctx) && !self.unreachable.contains(*block) && !doomed(theirs)).count()
        }).max().unwrap_or(0)
    }

    /// The thunk a `Guard(idx, t)` (`expected` `CType::Type(t)`) or a
    /// `GuardCType(idx, expected)` ends its block in when the context can't
    /// answer it.
    /// With `field`, the slot was just loaded from that hash key's field, of no
    /// stable type (`FieldType`), whose type is the one found too. See Note
    /// [Field types].
    /// A thunk finding out the type of STACK[idx] for a guard of `expected`.
    /// A function found gets its identity guarded too, unless the chain of
    /// thunks this one is in guards `identities` of them already, `MAX_VERSIONS`
    /// (Note [Call sites]).
    fn make_discovery_thunk(&self, block_id: BlockId, thunk_coro: Box<Gen>, idx: usize, expected: CType, field: Option<HashRef>, pc: SubPc, mut thunk_ctx: Rc<Context>, appends: bool, identities: usize) -> ThunkRef {

        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            // Each forcing patches the thunk where it was forced, in `block_id`: one
            // thunk can be the failure of more than one guard there.
            let mut block_id = block_id;
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
            //
            // A number's type is its encoding, found a step down the lattice at a
            // time: see Note [Integers].
            let mut thunk_coro  = thunk_coro.clone();
            let found_field = state.vals[state.base + idx].unbox().typeof_();
            let found = CType::Type(found_field);
            // An element of an array part whose kind is the element's
            // representation: the array's kind is tested in place of the
            // element's, and is known after. See Note [Array kinds].
            // The runtime kind of the array the element was loaded from.
            // An upvalue's table is read from the running closure's own upvalue; one
            // through another closure isn't, and its element is tested as any value.
            let array = thunk_ctx.element_of(idx).map(|table| {
                let value = match table {
                    Root::Slot(slot) => state.vals[state.base + slot as usize],
                    Root::Upvalue(j) => state.upvalue(owner, j as usize),
                    Root::Global(_) | Root::Arg(_) => unreachable!("an array read through a global or an argument"),
                };
                let LValue::Table(tab) = value.unbox() else { unreachable!("an element of an array part not of a table") };
                (table, tab.ro(owner).kind)
            });
            let kind_of = array.as_ref().filter(|(_, kind)| *kind == found_field.bit()).map(|(table, _)| table.clone());
            // A value the context knows is a number only has its encoding tested.
            let guard = if let Some(table) = &kind_of {
                Residual::GuardDynamic(match table {
                    Root::Slot(slot) => Rc::new(KindIs::new(found_field, &[*slot as usize])),
                    Root::Upvalue(j) => Rc::new(UpvalKindIs::new(*j as usize, found_field, &[])),
                    Root::Global(_) | Root::Arg(_) => unreachable!("an array read through a global or an argument"),
                })
            } else if thunk_ctx.types[idx] == CType::Number {
                Residual::NumericGuard { idx, expected: found_field }
            } else {
                Residual::Guard { idx, expected: found_field }
            };
            let mut forced_ctx = thunk_ctx.clone();;
            let mut forced_mut = Rc::make_mut(&mut forced_ctx);
            forced_mut.types[idx] = found.clone();
            if let Some(table) = kind_of {
                forced_mut.learn_kind(table, Kind::Of(found_field));
            }
            // An array of two representations or more stays mixed.
            if let Some((table, _)) = array.filter(|(_, kind)| kind.count_ones() > 1) {
                forced_mut.learn_kind(table, Kind::Mixed);
            }
            // A slot holding an upvalue's value tells of the upvalue: the type the
            // guard found, and past a function's identity guard below, which
            // function. See Note [Fragile information].
            if let Some(href) = field {
                forced_mut.hkeys[href.0 as usize].known_type = Some(Kind::Of(found_field));
            }
            let holds = forced_mut.holds(idx);
            if let Some(upvalue) = &holds {
                forced_mut.learn_upvalue(upvalue.clone(), found.clone());
            }
            // A slot holding a field's or a global's value tells of it too. See Note [Field facts].
            forced_mut.learn_held(idx, field, found.clone());
            debug!("forcing thunk with {} == {}", found, expected);
            // Continued as a guard the context answers would be, so the ways
            // finding out and knowing share the subblock.
            let (next, arg) = navigate(pc, &expected, &found);
            // TODO: search for if we already have a compatible block
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
            // If we're in the success block and the guarded value is a function, we can
            // also try to emit a guard to specialize the function value as well. This lets us
            // specialize code like `local print = print; print("xyz");`. Up to MAX_VERSIONS
            // of them: past that, the value is only a function. See Note [Call sites].
            let idx_ctype = Some(state.vals[state.base + idx].unbox().ctypeof_())
                .filter(|ctype| matches!(ctype, CType::NativeFunction(_) | CType::LuaFunction(_)))
                .filter(|_| identities < MAX_VERSIONS);
            let identities = identities + idx_ctype.is_some() as usize;
            // Push the same thunk down for the next value that fails the guard
            let fail_thunk = vm.make_discovery_thunk(block_id, thunk_coro.clone(), idx, expected.clone(), field, pc, thunk_ctx.clone(), false, identities);
            vm.blocks[block_id.0].instructions.push(Residual::Thunk(fail_thunk.clone()));
            if let Some(CType::NativeFunction(nf)) = &idx_ctype {
                // We know this original value has the correct native function, and so can compile
                // a block for it immediately.
                forced_mut.types[idx] = idx_ctype.clone().unwrap();
                if let Some(upvalue) = holds {
                    forced_mut.learn_upvalue(upvalue, idx_ctype.clone().unwrap());
                }
                forced_mut.learn_held(idx, field, idx_ctype.clone().unwrap());
                let guard_block = vm.subblock(owner, next, forced_ctx, thunk_coro, arg);
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
            } else if let Some(CType::LuaFunction(lclos)) = &idx_ctype {
                // Likewise we can do the same thing with statically known Lua functions
                forced_mut.types[idx] = idx_ctype.clone().unwrap();
                if let Some(upvalue) = holds {
                    forced_mut.learn_upvalue(upvalue, idx_ctype.clone().unwrap());
                }
                forced_mut.learn_held(idx, field, idx_ctype.clone().unwrap());
                let guard_block = vm.subblock(owner, next, forced_ctx, thunk_coro, arg);
                let proto = lclos.ro(owner).prototype.cast();
                vm.blocks[block_id.0].instructions.push(Residual::LuaGuard { idx, ptr: proto });
                vm.blocks[block_id.0].instructions.push(Residual::Thunk(fail_thunk));
                vm.blocks[block_id.0].instructions.push(Residual::Jump(guard_block));
            } else {
                let guard_block = vm.subblock(owner, next, forced_ctx, thunk_coro, arg);
                vm.blocks[block_id.0].instructions.push(Residual::Jump(guard_block));
            }

            debug!("after compiling thunk, blocks look like {:?}", vm.blocks);
        })))
    }

    /// The thunk an inlined callee's RETURN A B ends its block in: run, it lays out the return to
    /// the code after the call its frame's entry continues, and a jump to it. See Note [Inlined
    /// calls].
    fn make_inline_return_thunk(&self, block_id: BlockId, ctx: Rc<Context>, a: usize, b: u16, closes: bool) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            let Some(&CallstackEntry { ret: Return::Inlined(continuation), .. }) = state.callstack.last() else {
                unreachable!("an inlined call's return outside its frame")
            };
            // SAFETY: a continuation lives as long as the specializer does.
            let continuation = unsafe { &*(continuation as *const Continuation) };
            // In place, as for a call thunk. See Note [Thunk patching].
            let block = if vm.compiled(block_id) {
                let block = vm.new_block(vm.blocks[block_id.0].pc);
                vm.jump_thunk(block_id, thunk_pc, block);
                block
            } else {
                vm.blocks[block_id.0].instructions.truncate(thunk_pc);
                block_id
            };
            let after = vm.inline_return(owner, &ctx, continuation, a, b as usize);
            // A count of results known statically moves them as window ops in the caller's frame,
            // missing ones nil: values the JIT's window only renames. Every result up to the top
            // moves as a return's do.
            let moves = b == 0;
            let mut layout = vec![Residual::InlineReturn { a: a as u16, b, closes, call: continuation.a, moves }];
            if moves {
                layout.push(Residual::Arrive { a: continuation.a, c: continuation.c });
            } else {
                let (call, c, returned) = (continuation.a as usize, continuation.c as usize, b as usize - 1);
                for i in 0..if c == 0 { returned } else { c - 1 } {
                    let result: Rc<dyn Window> = if i < returned {
                        Rc::new(crate::generators::Move::new(&[call + 1 + a + i, call + i]))
                    } else {
                        Rc::new(crate::generators::LoadNil::new(&[call + i]))
                    };
                    layout.push(Residual::ExecWindow(result));
                }
                if c == 0 {
                    layout.push(Residual::ExecWindow(Rc::new(SetTop::new(call + returned, &[]))));
                }
            }
            layout.push(Residual::Jump(after));
            vm.blocks[block.0].instructions.extend(layout);
        })))
    }

    /// The caller's code after the inlined call `continuation` continues, for a return in the
    /// callee's code, in `ctx`, of RETURN A B: compiled from the caller's context before the call,
    /// less what the callee's code may have done to it, with the results' types. See Note [Inlined
    /// calls].
    fn inline_return(&mut self, owner: &mut Owner, ctx: &Context, continuation: &Continuation, a: usize, b: usize) -> BlockId {
        let (known, effects) = self.returned_context(owner, ctx, continuation, a, b);
        let callee = self.proto;
        #[cfg(feature = "tracing")]
        let (_callee, _known) = (self.traced_line(owner), known.tostring(owner));
        self.set_current(continuation.proto as LProto<'_, '_>);
        self.join_effects(owner, effects);
        let after = continuation.rest.block(self, owner, Rc::new(known));
        #[cfg(feature = "tracing")]
        crate::tracing::instant("spec", "inline_return", &[
            ("line", self.traced_line(owner).into()),
            ("callee", _callee.into()),
            ("after", continuation.rest.pc().into()),
            ("block", after.0.into()),
            ("context", _known.as_str().into()),
        ]);
        self.set_current(callee);
        after
    }

    /// The caller's context after the inlined call `continuation`, for a return in the callee's
    /// code, in `ctx`, of RETURN A B, and what the callee's code may have done to the caller's: the
    /// caller's context before the call, less that, with the results' types. See Note [Inlined
    /// calls].
    fn returned_context(&mut self, owner: &mut Owner, ctx: &Context, continuation: &Continuation, a: usize, b: usize) -> (Context, Effects) {
        let effects = ctx.inline.last().expect("an inlined call's frame").effects;
        let caller = &continuation.caller;
        let mut known = caller.clone();
        // Its frames as the callee's code made them. See Note [Peephole fusion] in `peephole`.
        for (frame, now) in known.inline.iter_mut().zip(&ctx.inline) {
            frame.made = now.made;
        }
        // The hash keys the callee leaves, in the witnesses it shared: the caller's own it kept
        // are the caller's again, and any other, of the callee's frame or put in place of one of
        // the caller's, is free. See Note [Inlined calls].
        // A parameter still holding the table it was passed has its hash keys the caller's slot's.
        let frame = ctx.inline.last().expect("an inlined call's frame");
        let passed = |slot: usize| frame.owner(ctx, slot);
        let mut gained: Vec<(usize, HashRef)> = Vec::new();
        known.hkeys = ctx.hkeys.iter().enumerate().map(|(i, hkey)| match caller.hkeys.get(i) {
            Some(mine) if !hkey.orphan() && hkey.idx == OUTER && !mine.orphan() => mine.clone(),
            _ if !hkey.orphan() && hkey.place == Place::Register && let Some(owner) = passed(hkey.idx) => {
                let mut theirs = hkey.clone();
                theirs.idx = owner;
                theirs.clear_checks();
                gained.push((owner, HashRef(i as u8)));
                theirs
            },
            _ => {
                let mut free = hkey.clone();
                free.known_type = None;
                free.clear_checks();
                free
            },
        }).collect();
        // A callee's version knowing fewer hash keys than the caller had (Note [Version
        // compatibility]) leaves fewer: the caller's past them are free, as the callee may have
        // put its own there.
        for i in known.hkeys.len()..caller.hkeys.len() {
            let mut free = caller.hkeys[i].clone();
            free.known_type = None;
            free.clear_checks();
            known.hkeys.push(free);
        }
        // A shape keeps the caller's hash keys that came back as they were, and gains its slot's.
        let unchanged = |href: &HashRef| {
            let (mine, back) = (caller.hkeys.get(href.0 as usize), known.hkeys.get(href.0 as usize));
            mine.zip(back).is_some_and(|(mine, back)| !back.orphan() && mine.idx == back.idx && mine.key == back.key && mine.place == back.place && mine.chain == back.chain)
        };
        for slot in 0..known.types.len() {
            let CType::Shape(of, hrefs) = &known.types[slot] else { continue };
            let mut kept: SmallVec<[HashRef; 4]> = hrefs.iter().filter(|href| unchanged(href)).cloned().collect();
            for &(owner, href) in &gained {
                if owner == slot && !kept.contains(&href) {
                    kept.push(href);
                }
            }
            known.types[slot] = if kept.is_empty() { CType::Type(*of) } else { CType::Shape(*of, kept) };
        }
        effects.apply(owner, &mut known, &continuation.captured);
        // See Note [Upvalue paths].
        let (call, c) = (continuation.a as usize, continuation.c as usize);
        let returned = (b != 0).then(|| b - 1);
        let count = if c == 0 { returned.unwrap_or(0) } else { c - 1 };
        let fields: Vec<[Label; 1]> = (0..unsafe { (*self.proto).upval_count }).map(|n| [Label::Upvalue(n)]).collect();
        let map: Vec<(Loc, Loc)> = continuation.closure.into_iter()
            .flat_map(|closure| fields.iter().enumerate().map(move |(n, path)| (Loc { root: closure, path }, Loc::root(Root::Upvalue(n as u8)))))
            .chain((0..count.min(returned.unwrap_or(0))).map(|i| (Loc::root(Root::Slot((call + i) as u16)), Loc::root(Root::Slot((a + i) as u16)))))
            // A callee's globals are its caller's. See Note [Field facts].
            .chain(ctx.values.roots().filter(|root| matches!(root, Root::Global(_))).map(|root| (Loc::root(root), Loc::root(root))))
            .collect();
        known.values.overlay(&ctx.closing(0), &map);
        // What it learned of the values it was passed, the caller's places holding them learn:
        // the same values, of which the caller knows the rest. See Note [Inlined calls].
        for &(n, root) in &continuation.args {
            for fact in ctx.values.facts(Loc::root(Root::Arg(n))) {
                known.values.learn(Loc::root(root), fact.clone());
            }
        }
        let slots = known.types.len();
        for i in (0..count).filter(|i| call + i < slots) {
            known.types[call + i] = match returned {
                Some(returned) if i < returned => match ctx.slot(a + i) {
                    CType::Shape(of, _) => CType::Type(of),
                    ctype => ctype,
                },
                Some(_) => CType::Type(LType::Nil),
                None => CType::Unknown,
            };
        }
        known.top = if c == 0 { returned.map(|returned| call + returned) } else { None };
        // A parameter the callee's code never wrote holds what it was passed still: its slot past
        // the results holds the caller's value. See Note [Inlined calls].
        for &(n, root) in &continuation.args {
            let slot = call + 1 + n as usize;
            if slot >= call + count && slot < slots && ctx.values.members(Loc::root(Root::Arg(n))).contains(&Root::Slot(n as u16)) {
                known.values.assign(Root::Slot(slot as u16), Loc::root(root));
                known.types[slot] = match ctx.slot(n as usize) {
                    CType::Shape(of, _) => CType::Type(of),
                    ctype => ctype,
                };
            }
        }
        (known, effects)
    }

    /// The thunk a call to R(A) of the context `calling`, continuing at
    /// `after` (as `After::block`), ends its block in, or, not `appends`, a guard's failure is: run,
    /// it lays out a call for the function in R(A), guarding its identity and
    /// chaining a thunk for the next onto the guard's failure, while its chain
    /// guards fewer than `MAX_VERSIONS` (`identities`); past that, or for what
    /// isn't a function, a generic call. With a `continuation`, the context
    /// before the call less the callee's frame, the caller's captured slots
    /// below it, and the pc after it, a Lua function's call continues at a thunk
    /// specializing it to the return. See Notes [Call sites], [Call
    /// continuations] and [Call effects].
    fn make_call_thunk(&self, block_id: BlockId, calling: Rc<Context>, coro: Box<Gen>, restart: Option<(Pc, Restart, bool)>, pc: SubPc, a: usize, b: usize, c: usize, after: After, continuation: Option<(Rc<Context>, Rc<[usize]>, Rest)>, identities: usize, appends: bool) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            // In place, unless the thunk's JIT code can only be patched to a jump, or it
            // is a guard's failure, with the rest of the layout after it. See Note
            // [Thunk patching].
            let mut block = if !appends || vm.compiled(block_id) {
                let block = vm.new_block(vm.blocks[block_id.0].pc);
                vm.jump_thunk(block_id, thunk_pc, block);
                block
            } else {
                vm.blocks[block_id.0].instructions.truncate(thunk_pc);
                block_id
            };
            let (a16, b16, c16) = (a as u16, b as u16, c as u16);
            let next = |vm: &Specializer, block: BlockId| Residual::Thunk(vm.make_call_thunk(block, calling.clone(), coro.clone(), restart.clone(), pc, a, b, c, after.clone(), continuation.clone(), identities + 1, false));
            let mut layout = vec![];
            match state.vals[state.base + a].unbox() {
                LValue::LClosure(lclos) if matches!(calling.types[a], CType::LuaFunction(_)) || identities < MAX_VERSIONS => {
                    let proto = lclos.ro(owner).prototype;
                    if !matches!(calling.types[a], CType::LuaFunction(_)) {
                        layout.push(Residual::LuaGuard { idx: a, ptr: proto.cast() });
                        layout.push(next(vm, block));
                    }
                    // A call a continuation decided to inline in a context its callee's entry
                    // accepts this one's in inlines from the first, as does one making a generic
                    // for's iterator. See Note [Inlined calls].
                    if let Some((ctx, captured, rest)) = &continuation
                        && inlines(&calling, unsafe { &*vm.proto }, unsafe { &*proto }, a)
                    {
                        let callee = proto as LProto<'static, 'static>;
                        let call = Location(block, vm.blocks[block.0].instructions.len() + layout.len());
                        let entry = Self::inline_frame(&calling, callee, call, vm.proto as LProto<'static, 'static>, a, b);
                        let mut known = entry.clone();
                        known.inline = Vec::new();
                        let decided = vm.inlined.get(&(vm.proto, pc, proto)).is_some_and(|decided| decided.iter().any(|decided| decided.accepts(&known)));
                        if decided || makes_iterator(unsafe { &*vm.proto }, pc.0, a) {
                            vm.blocks[block.0].instructions.extend(layout);
                            // The callee's code goes on from the peephole as it was at the call,
                            // holding what it held, but what can't go on into it, laid out first.
                            // See Note [Peephole fusion] in `peephole`.
                            let (laid, kept) = entering(&coro.held, &calling, callee, a, b);
                            let continuation = vm.continuation(&calling, ctx, captured, rest, a, c);
                            let shift = vm.inline_call(owner, state, block, callee, a, b, entry, continuation, kept);
                            vm.held_first(owner, block, pc, &calling, laid, &restart, &mut vec![], Some(shift));
                            return;
                        }
                    }
                    // A call observes what the peephole holds: laid out first, where its
                    // continuation inlining it goes on from instead. See Note [Peephole fusion] in
                    // `peephole`.
                    let start = Location(block, vm.blocks[block.0].instructions.len() + layout.len());
                    block = vm.held_first(owner, block, pc, &calling, coro.held.clone(), &restart, &mut layout, None);
                    let (stack, vararg) = unsafe { ((*proto).max_stack, (*proto).is_vararg != 0) };
                    let entry = Rc::new(entry_context(&calling, unsafe { &*proto }, a, b));
                    let off = vm.blocks[block.0].instructions.len() + layout.len();
                    layout.push(Residual::LuaCall { entry: CallEntry::Context(entry), a: a16, b: b16, c: c16, stack, vararg, callee: proto as LProto<'static, 'static> });
                    if let Some((ctx, captured, rest)) = &continuation {
                        // See Notes [Call continuations] and [Inlined calls].
                        let call = InlineCall { block, off, pc, callee: proto as LProto<'static, 'static>, calling: calling.clone(), b, coro: coro.clone(), start, restart: restart.clone() };
                        layout.push(Residual::Thunk(vm.make_continuation_thunk(block, ctx.clone(), captured.clone(), rest.clone(), a, c, after.clone(), Some(Rc::new(call)), 0, true)));
                        // Where its returns go on. See Note [Watched tables].
                        vm.continuation_sites.insert(Location(block, off + 1), ContinuationSite { ctx: ctx.clone(), captured: captured.clone(), rest: rest.clone(), a, c, after: after.clone() });
                        vm.blocks[block.0].instructions.extend(layout);
                        return;
                    }
                    layout.push(Residual::Arrive { a: a16, c: c16 });
                    // See Note [Call effects].
                    vm.join_effects(owner, Effects::OPAQUE);
                },
                // An error raised in it continues after it. See Note [Errors].
                LValue::NClosure(nf) if nf.is_protected_call() && identities < MAX_VERSIONS => {
                    layout.push(Residual::NativeGuard { idx: a, ptr: nf.get_ptr() });
                    layout.push(next(vm, block));
                    block = vm.held_first(owner, block, pc, &calling, coro.held.clone(), &restart, &mut layout, None);
                    let after = after.block(vm, owner);
                    layout.extend(Self::protected_call(a, b, c, after));
                    layout.push(Residual::Jump(after));
                    vm.blocks[block.0].instructions.extend(layout);
                    vm.join_effects(owner, Effects::OPAQUE);
                    return;
                },
                LValue::NClosure(nf) if identities < MAX_VERSIONS => {
                    layout.push(Residual::NativeGuard { idx: a, ptr: nf.get_ptr() });
                    layout.push(next(vm, block));
                    // Past the guard, a native with a generator is compiled by it, as an opcode is,
                    // and the code after the call is a version. See Note [Native generators] in
                    // `library`.
                    if let (Some(generator), After::Version(..)) = (nf.generator(), &after) {
                        vm.blocks[block.0].instructions.extend(layout);
                        // Compiled by the peephole as it was at the call, holding what it held.
                        let mut body = coro.clone();
                        body.generate(generator(nf.native(), a, b, c));
                        let outer = std::mem::replace(&mut vm.instruction, restart.clone());
                        vm.entering = true;
                        let compiled = vm.compile_one(owner, pc, calling.clone(), body, ResumeArg::Start, block);
                        vm.instruction = outer;
                        if let Some((next, ctx, _, held)) = compiled {
                            debug_assert!(held.is_empty(), "a native's call holding what the peephole held past it");
                            let ctx = vm.jumping(owner, ctx, next);
                            let version = After::Version(next, ctx).block(vm, owner);
                            vm.blocks[block.0].instructions.push(Residual::Jump(version));
                        }
                        return;
                    }
                    block = vm.held_first(owner, block, pc, &calling, coro.held.clone(), &restart, &mut layout, None);
                    // Past the guard the native is known: it runs as its window op if
                    // the call's arguments have the types the op assumes. See Note
                    // [Native windows].
                    let window = native_op(&calling, &nf, a, b, c)
                        .filter(|(end, op)| (a + 1..*end).all(|slot| op.args.accepts(&calling.slot(slot))));
                    // What the code after an effect-free call knows: its context before the
                    // call, but for the callee's frame, and a window op's result.
                    let mut known = continuation.as_ref().map(|(before, _, rest)| ((**before).clone(), rest.clone()));
                    if let Some((_, op)) = window {
                        layout.push(Residual::ExecWindow(op.window));
                        if c == 0 {
                            layout.push(Residual::ExecWindow(Rc::new(SetTop::new(a + 1, &[]))));
                        }
                        if let Some((known, _)) = &mut known {
                            known.types[a] = op.result;
                            known.top = (c == 0).then_some(a + 1);
                        }
                    } else {
                        layout.push(Residual::NativeCall { nf: nf.native(), a: a16, b: b16, c: c16 });
                        // A native may allocate (a table, a string).
                        layout.push(Residual::GC);
                        if let Some((known, _)) = &mut known {
                            known.top = None;
                        }
                        // See Note [Call effects].
                        if !nf.is_pure() {
                            vm.join_effects(owner, Effects::OPAQUE);
                            known = None;
                        }
                    }
                    // See Note [Library natives] in `library`.
                    if let Some((known, rest)) = known {
                        let after = match rest {
                            Rest::Next(pc) => {
                                let known = vm.jumping(owner, Rc::new(known), pc);
                                After::Version(pc, known).block(vm, owner)
                            },
                            rest => rest.block(vm, owner, Rc::new(known)),
                        };
                        layout.push(Residual::Jump(after));
                        vm.blocks[block.0].instructions.extend(layout);
                        return;
                    }
                },
                _ => {
                    block = vm.held_first(owner, block, pc, &calling, coro.held.clone(), &restart, &mut layout, None);
                    layout.push(Residual::Call { a: a16, b: b16, c: c16 });
                    layout.push(Residual::Arrive { a: a16, c: c16 });
                    // It may call a native, which may allocate.
                    layout.push(Residual::GC);
                    // See Note [Call effects].
                    vm.join_effects(owner, Effects::OPAQUE);
                },
            }
            layout.push(Residual::Jump(after.block(vm, owner)));
            vm.blocks[block.0].instructions.extend(layout);
        })))
    }

    /// The block a call thunk's layout goes on in past `layout`, laid out in `block`: past `held`,
    /// what the peephole held at the call, laid out from the call's `restart`, if anything, or
    /// `to`, jumped to past it. See Note [Peephole fusion] in `peephole`.
    fn held_first(&mut self, owner: &mut Owner, block: BlockId, pc: SubPc, ctx: &Rc<Context>, held: crate::peephole::Spells, restart: &Option<(Pc, Restart, bool)>, layout: &mut Vec<Residual>, to: Option<BlockId>) -> BlockId {
        self.blocks[block.0].instructions.extend(layout.drain(..));
        if held.is_empty() {
            if let Some(to) = to {
                self.blocks[block.0].instructions.push(Residual::Jump(to));
            }
            return block;
        }
        let rest = to.unwrap_or_else(|| self.new_block(self.blocks[block.0].pc));
        let outer = std::mem::replace(&mut self.instruction, restart.clone());
        self.entering = true;
        self.compile_one(owner, pc, ctx.clone(), Gen::holding(held, crate::generators::emit_lay_out_to(rest)), ResumeArg::Start, block);
        self.instruction = outer;
        rest
    }

    /// What inlining the callee entered at its version `entry` would cost, as its first call ran it,
    /// returning from block `exit`: its code from `entry` that reaches `exit`, as far as it is
    /// compiled, or `None` if that code loops, or none of it from `entry` does. See Note [Inlined
    /// calls].
    fn inline_cost(&self, owner: &Owner, entry: BlockId, exit: BlockId, callee: LProto<'static, 'static>) -> Option<InlineCost> {
        type Blocks = std::collections::HashSet<BlockId, rustc_hash::FxBuildHasher>;
        // The blocks code goes on to within the callee's, its calls of other functions apart: all
        // of each block's code, as the call ran it, a rebuild's cut in it or not.
        let flow = |block: BlockId| -> SmallVec<[BlockId; 4]> {
            self.blocks[block.0].instructions.iter().flat_map(|res| -> SmallVec<[BlockId; 2]> {
                match res {
                    Residual::Jump(target) | Residual::PatchableJump(target) => smallvec::smallvec![*target],
                    Residual::Branch { hot, cold } => smallvec::smallvec![*hot, *cold],
                    Residual::Select(targets) => targets.iter().map(|(_, target)| *target).collect(),
                    _ => SmallVec::new(),
                }
            }).collect()
        };
        let mut reached = Blocks::default();
        // Each reached block's predecessors among them.
        let mut from: HashMap<BlockId, SmallVec<[BlockId; 2]>, rustc_hash::FxBuildHasher> = HashMap::default();
        let mut work = vec![entry];
        while let Some(block) = work.pop() {
            if reached.insert(block) {
                for target in flow(block) {
                    from.entry(target).or_default().push(block);
                    work.push(target);
                }
            }
        }
        // Those that reach the exit the call took, back from it.
        let mut path = Blocks::default();
        let mut work: Vec<BlockId> = reached.contains(&exit).then_some(exit).into_iter().collect();
        while let Some(block) = work.pop() {
            if path.insert(block) {
                work.extend(from.get(&block).into_iter().flatten().copied());
            }
        }
        // A cycle among them is a loop.
        let mut done = Blocks::default();
        let mut active = Blocks::default();
        fn cycles(block: BlockId, path: &Blocks, flow: &dyn Fn(BlockId) -> SmallVec<[BlockId; 4]>, done: &mut Blocks, active: &mut Blocks) -> bool {
            if done.contains(&block) {
                return false;
            }
            if !active.insert(block) {
                return true;
            }
            let found = flow(block).into_iter().filter(|target| path.contains(target)).any(|target| cycles(target, path, flow, done, active));
            active.remove(&block);
            done.insert(block);
            found
        }
        // The decision, for the trace: what it measured, or why it didn't.
        #[cfg(feature = "tracing")]
        let traced = |why: &str, measured: Option<InlineCost>| crate::tracing::instant("spec", "inline_cost", &[
            ("line", self.traced_line(owner).into()),
            ("callee", (unsafe { (*callee).line_defined } as u64).into()),
            ("entry", entry.0.into()),
            ("blocks", path.len().into()),
            ("cost", measured.map_or(0, |m| m.cost).into()),
            ("reused", measured.map_or(0, |m| m.reused).into()),
            ("inlines", u64::from(measured.is_some_and(InlineCost::inlines)).into()),
            ("why", why.into()),
        ]);
        // With none from the entry, what the call ran isn't compiled as it ran: not measured, it
        // doesn't inline.
        if !path.contains(&entry) {
            #[cfg(feature = "tracing")]
            traced("unmeasured", None);
            return None;
        }
        if cycles(entry, &path, &flow, &mut done, &mut active) {
            #[cfg(feature = "tracing")]
            traced("loops", None);
            return None;
        }
        let mut measured = InlineCost { cost: 0, reused: 0 };
        for &block in &path {
            // The slots the block loaded from upvalues, still holding what they loaded.
            let mut upvalued: SmallVec<[usize; 4]> = SmallVec::new();
            for res in &self.blocks[block.0].instructions {
                measured.cost += match res {
                    Residual::Jump(_) | Residual::PatchableJump(_) | Residual::Branch { .. } | Residual::Select(_) | Residual::Thunk(_) | Residual::Ret(..)
                        | Residual::ReturnedFrom(_) | Residual::Arrive { .. } | Residual::Arrived { .. } | Residual::GC => 0,
                    _ => 1,
                };
                match res {
                    Residual::ExecWindow(w) => {
                        let written = w.operands().iter().zip(w.accesses()).filter(|(_, access)| access.writes()).map(|(&slot, _)| slot);
                        let loads = matches!(w.name(), "GetUpval" | "HeldUpval" | "NativeUpval");
                        for slot in written {
                            upvalued.retain(|held| *held != slot);
                            if loads {
                                upvalued.push(slot);
                            }
                        }
                    }
                    Residual::Guard { idx, .. } | Residual::NativeGuard { idx, .. } | Residual::LuaGuard { idx, .. } if upvalued.contains(idx) => measured.reused += 1,
                    Residual::GuardWitness { .. } | Residual::HashGuard { .. } | Residual::EpochCheck { .. } => measured.reused += 1,
                    _ => {}
                }
            }
        }
        #[cfg(feature = "tracing")]
        traced("measured", Some(measured));
        let _ = (owner, callee);
        Some(measured)
    }

    /// The entry context of the inlined call `call` of R(A) with B in `calling`, of `callee`, by
    /// the function `proto`. See Note [Inlined calls].
    fn inline_frame(calling: &Context, callee: LProto<'static, 'static>, call: Location, proto: LProto<'static, 'static>, a: usize, b: usize) -> Context {
        // A table parameter's hash keys are its caller's slot's. See Note [Inlined calls].
        let params = unsafe { (*callee).param_count } as usize;
        let passed = (0..params).filter_map(|param| match calling.slot(a + 1 + param) {
            CType::Shape(_, hrefs) => hrefs.first().map(|href| calling.hkeys[href.0 as usize].idx).filter(|&owner| owner < a)
                .map(|owner| (param as u16, owner as u16)),
            _ => None,
        }).collect();
        let frame = InlineFrame {
            call, proto, a: a as u16, effects: Effects::NONE, passed, made: Made::No,
            b: b as u16, params: unsafe { (*callee).param_count }, stack: unsafe { (*callee).max_stack }, cells: 0, continuation: std::ptr::null(),
            closure: match calling.values.fact(Loc::root(Root::Slot(a as u16)), VALUE) {
                Some(&Known::Value(bits)) => Some(bits),
                _ => None,
            },
        };
        inline_entry(calling, unsafe { &*callee }, a, b, frame)
    }

    /// The code after the inlined call of R(A) with C in `calling`, by the running function: the
    /// context before the call `caller`, less the callee's frame (`captured` its slots below the call
    /// its closures captured), continuing as `rest`. See Note [Inlined calls].
    fn continuation(&self, calling: &Context, caller: &Context, captured: &Rc<[usize]>, rest: &Rest, a: usize, c: usize) -> Continuation {
        Continuation {
            proto: self.proto as LProto<'static, 'static>,
            caller: caller.clone(),
            captured: captured.clone(),
            a: a as u16,
            c: c as u16,
            // A place below the call holding the callee's closure. See Note [Upvalue paths].
            closure: calling.values.members(Loc::root(Root::Slot(a as u16))).into_iter().find(|root| !matches!(root, Root::Slot(slot) if *slot as usize >= a)),
            // What the callee learns of its arguments' values. See Note [Inlined calls].
            args: (a + 1..calling.types.len()).flat_map(|arg| {
                calling.values.members(Loc::root(Root::Slot(arg as u16))).into_iter()
                    .filter(|root| !matches!(root, Root::Slot(slot) if *slot as usize >= a))
                    .map(move |root| ((arg - a - 1) as u8, root))
            }).collect(),
            rest: rest.clone(),
        }
    }

    /// The block an inlined call of R(A) with B, of `callee`, made in `block`, moves to the
    /// callee's frame in, then goes on to its version for `entry`, its returns continuing
    /// `continuation`. See Note [Inlined calls].
    fn inline_call(&mut self, owner: &mut Owner, state: &mut RunState<'_, '_>, block: BlockId, callee: LProto<'static, 'static>, a: usize, b: usize, entry: Context, continuation: Continuation, held: crate::peephole::Spells) -> BlockId {
        // The outermost function's frame holds the callee's.
        let outermost = entry.inline.first().expect("an inlined call's frame").proto;
        if unsafe { (*outermost).frame_size.grow(inline_offset(&entry) + (*callee).max_stack as usize) } {
            state.fit_frames(owner);
            #[cfg(feature = "jit")]
            self.jctx.frame_grew(outermost as usize, unsafe { (*outermost).frame_size.get() });
        }
        #[cfg(feature = "tracing")]
        let (_line, _entry, _after) = (self.traced_line(owner), entry.tostring(owner), continuation.rest.pc());
        let continuation = Rc::new(continuation);
        let pointer = Rc::as_ptr(&continuation);
        self.continuations.push(continuation);
        let caller = self.proto;
        self.set_current(callee as LProto<'_, '_>);
        self.versions.entry(self.proto).or_insert_with(|| HashMap::default());
        // Its frame's cells its entry's facts are about: the JIT fills them as the frame is
        // entered. See Note [Upvalue cells].
        let own = (1u32 << UPVALUE_CELLS) - 1;
        let cells = entry.filled_cells() & own << (entry.depth() * UPVALUE_CELLS);
        // Its code from the call's block, its frame unmade until code observes it, so code naming
        // only its slots runs in its caller's, and code laying out nothing folds into it. See Note
        // [Peephole fusion] in `peephole`.
        let shift = self.new_block(self.blocks[block.0].pc);
        let mut entry = entry;
        let frame = entry.inline.last_mut().expect("an inlined call's frame");
        (frame.cells, frame.continuation) = (cells, pointer);
        self.compile_holding(owner, 0, Rc::new(entry), shift, held);
        self.set_current(caller);
        #[cfg(feature = "tracing")]
        crate::tracing::instant("spec", "inline", &[
            ("line", _line.into()),
            ("callee", (unsafe { (*callee).line_defined } as u64).into()),
            ("after", _after.into()),
            ("call_block", block.0.into()),
            ("shift", shift.0.into()),
            ("entry", shift.0.into()),
            ("context", _entry.as_str().into()),
        ]);
        shift
    }

    /// The thunk a Lua function's call continues at, in `block_id`, or, not
    /// `appends`, a continuation guard's failure is: run, just after a return,
    /// it lays out a guard on that return, chaining a thunk for the next onto
    /// its failure, and on its success the call's results, of the count the
    /// return gives, and a version of the code after the call at `pc` knowing
    /// their types and the callee's effects, from `ctx`, the context before the
    /// call less the callee's frame (`captured` its slots below the call's that
    /// its closures captured); while its chain guards fewer than `MAX_VERSIONS`
    /// (`identities`). Past that, or for a return that doesn't know what it
    /// returns, the results, and `after` (as `After::block`). See Notes [Call continuations] and
    /// [Call effects].
    fn make_continuation_thunk(&self, block_id: BlockId, ctx: Rc<Context>, captured: Rc<[usize]>, rest: Rest, a: usize, c: usize, after: After, inline: Option<Rc<InlineCall>>, identities: usize, appends: bool) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            // The call it continues, laid out just before it, inlined from now on: this return,
            // from its frame, continues as any other. See Note [Inlined calls].
            #[cfg(feature = "tracing")]
            if let Some(call) = &inline {
                let refused = if vm.compiled(call.block) {
                    Some("compiled")
                } else if !matches!(vm.blocks[call.block.0].instructions.get(call.off), Some(Residual::LuaCall { .. })) {
                    Some("relaid")
                } else if !inlines(&call.calling, unsafe { &*vm.proto }, unsafe { &*call.callee }, a) {
                    Some("policy")
                } else {
                    None
                };
                if let Some(reason) = refused {
                    crate::tracing::instant("spec", "inline_refused", &[
                        ("line", vm.traced_line(owner).into()),
                        ("callee", (unsafe { (*call.callee).line_defined } as u64).into()),
                        ("call_block", call.block.0.into()),
                        ("reason", reason.into()),
                    ]);
                }
            }
            if let Some(call) = &inline
                && !vm.compiled(call.block) && !vm.compiled(call.start.0)
                && let Some(&Residual::LuaCall { entry: CallEntry::Block(entry), .. }) = vm.blocks[call.block.0].instructions.get(call.off)
                && inlines(&call.calling, unsafe { &*vm.proto }, unsafe { &*call.callee }, a)
                && state.returned & !0xffff_ffff == crate::vm::RETURNED
                && vm.inline_cost(owner, entry, Location::unpack(crate::vm::PackedLocation::from_bits(state.returned_at as usize)).0, call.callee).is_some_and(InlineCost::inlines)
            {
                let entry = Self::inline_frame(&call.calling, call.callee, Location(call.block, call.off), vm.proto as LProto<'static, 'static>, a, call.b);
                let mut decided = entry.clone();
                decided.inline = Vec::new();
                vm.inlined.entry((vm.proto, call.pc, call.callee as LProto<'_, '_>)).or_default().push(decided);
                let continuation = vm.continuation(&call.calling, &ctx, &captured, &rest, a, c);
                // From the call as it was, the peephole holding what it held there: where what it
                // held is laid out goes on into the callee's code instead. See Note [Peephole
                // fusion] in `peephole`.
                let (laid, kept) = entering(&call.coro.held, &call.calling, call.callee, a, call.b);
                let shift = vm.inline_call(owner, state, call.start.0, call.callee, a, call.b, entry, continuation, kept);
                let into = if laid.is_empty() {
                    shift
                } else {
                    let edge = vm.new_block(vm.blocks[call.start.0.0].pc);
                    vm.held_first(owner, edge, call.pc, &call.calling, laid, &call.restart, &mut vec![], Some(shift));
                    edge
                };
                let Location(block, off) = call.start;
                if off < vm.blocks[block.0].instructions.len() {
                    vm.blocks[block.0].instructions[off] = Residual::Jump(into);
                } else {
                    vm.blocks[block.0].instructions.push(Residual::Jump(into));
                }
            }
            // In place, as for a call thunk. See Note [Thunk patching].
            let block = if !appends || vm.compiled(block_id) {
                let block = vm.new_block(vm.blocks[block_id.0].pc);
                vm.jump_thunk(block_id, thunk_pc, block);
                block
            } else {
                vm.blocks[block_id.0].instructions.truncate(thunk_pc);
                block_id
            };
            let (a16, c16) = (a as u16, c as u16);
            let returned = state.returned;
            let results = (returned & !0xffff_ffff == crate::vm::RETURNED && identities < MAX_VERSIONS)
                .then(|| vm.returns.get((returned & UNKNOWN_RETURN as u64) as usize).cloned())
                .flatten();
            let mut layout = vec![];
            match results {
                Some(results) => {
                    // What the callee did, which the caller's code after the call does
                    // too. See Note [Call effects].
                    let effects = Effects(((returned & 0xffff_ffff) >> crate::vm::EFFECTS_SHIFT) as u16);
                    vm.join_effects(owner, effects);
                    let mut known = (*ctx).clone();
                    effects.apply(owner, &mut known, &captured);
                    let count = if c == 0 { results.len() } else { c - 1 };
                    let slots = known.types.len();
                    for i in (0..count).filter(|i| a + i < slots) {
                        known.types[a + i] = results.get(i).cloned().unwrap_or(CType::Type(LType::Nil));
                    }
                    if c == 0 {
                        known.top = Some(a + results.len());
                    }
                    // Not `jumping`: the code after the call is reached by falling through,
                    // and the results are usually in temporaries it reads.
                    let version = rest.block(vm, owner, Rc::new(known));
                    layout.push(Residual::ReturnedFrom(returned));
                    layout.push(Residual::Thunk(vm.make_continuation_thunk(block, ctx.clone(), captured.clone(), rest.clone(), a, c, after.clone(), None, identities + 1, false)));
                    layout.push(Residual::Arrived { a: a16, c: c16, returned: results.len() as u16 });
                    layout.push(Residual::Jump(version));
                },
                None => {
                    layout.push(Residual::Arrive { a: a16, c: c16 });
                    layout.push(Residual::Jump(after.block(vm, owner)));
                    // See Note [Call effects].
                    vm.join_effects(owner, Effects::OPAQUE);
                },
            }
            vm.blocks[block.0].instructions.extend(layout);
        })))
    }

    /// The thunk a TAILCALL ends its block in, or, not `appends`, a guard's
    /// failure is: run, it lays out a tail call of the Lua function in R(A),
    /// guarding its identity and chaining a thunk for the next onto the guard's
    /// failure, while its chain guards fewer than `MAX_VERSIONS`
    /// (`identities`); a call of a native, guarded likewise, and a return of its
    /// results; past that, or for what isn't a function, a generic call and a
    /// return of its results. See Note [Tail calls].
    /// The layout of a protected call (`pcall`) in R(A) with B and C, an error
    /// raised in it continuing at `after`: its handler pushed, a call of R(A+1)
    /// with the rest of the arguments, and on its return the handler popped and
    /// true before its results. See Note [Errors].
    fn protected_call(a: usize, b: usize, c: usize, after: BlockId) -> Vec<Residual> {
        if b == 1 {
            return vec![Residual::Exec(ResidualExec::new("pcall_argument", Rc::new(|_owner, state| {
                state.raise(LBoxed::box_lvalue(LValue::OwnedString(crate::gc::Gc::string(b"bad argument #1 to 'pcall' (value expected)"))));
            })))];
        }
        // One fewer argument, and one fewer result, but for none (C = 1) or all
        // (C = 0) of them.
        let (callee_b, callee_c) = (b.saturating_sub(1), if c <= 1 { c } else { c - 1 });
        let c16 = c as u16;
        vec![
            Residual::Exec(ResidualExec::new("pcall", Rc::new(move |_owner, state| {
                // Frames JIT code called are the callstack's too. See Note [Frame ops].
                let handler = crate::vm::Handler { depth: state.callstack.len() + state.jit_depth, slot: state.base + a, c: c16, after };
                state.handlers.push(handler);
            }))),
            Residual::Call { a: a as u16 + 1, b: callee_b as u16, c: callee_c as u16 },
            Residual::Arrive { a: a as u16 + 1, c: callee_c as u16 },
            Residual::Exec(ResidualExec::new("pcall_return", Rc::new(move |_owner, state| {
                state.handlers.pop();
                state.vals[state.base + a] = LBoxed::from_bool(true);
            }))),
            // It may call a native, which may allocate.
            Residual::GC,
        ]
    }

    fn make_tail_call_thunk(&self, block_id: BlockId, site: Rc<TailSite>, identities: usize, appends: bool) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            // In place, as for a call thunk. See Note [Thunk patching].
            let block = if !appends || vm.compiled(block_id) {
                let block = vm.new_block(vm.blocks[block_id.0].pc);
                vm.jump_thunk(block_id, thunk_pc, block);
                block
            } else {
                vm.blocks[block_id.0].instructions.truncate(thunk_pc);
                block_id
            };
            let TailSite { ref calling, pc, a, b, closes, vararg, effects } = *site;
            let (a16, b16) = (a as u16, b as u16);
            let next = |vm: &Specializer| Residual::Thunk(vm.make_tail_call_thunk(block, site.clone(), identities + 1, false));
            // The results of what it calls, every one, returned.
            let ret = Residual::Ret(pc, a as u8, 0, closes, vararg, UNKNOWN_RETURN, effects);
            let mut layout = vec![];
            match state.vals[state.base + a].unbox() {
                LValue::LClosure(lclos) if matches!(calling.types[a], CType::LuaFunction(_)) || identities < MAX_VERSIONS => {
                    let proto = lclos.ro(owner).prototype;
                    if !matches!(calling.types[a], CType::LuaFunction(_)) {
                        layout.push(Residual::LuaGuard { idx: a, ptr: proto.cast() });
                        layout.push(next(vm));
                    }
                    let entry = Rc::new(entry_context(calling, unsafe { &*proto }, a, b));
                    let callee_effects: *const Cell<Effects> = vm.effects_of(proto.cast());
                    layout.push(Residual::TailCall { entry: CallEntry::Context(entry), a: a16, b: b16, closes, vararg, effects, callee_effects });
                },
                // Returning its results, or false and the error. See Note [Errors].
                LValue::NClosure(nf) if nf.is_protected_call() && identities < MAX_VERSIONS => {
                    layout.push(Residual::NativeGuard { idx: a, ptr: nf.get_ptr() });
                    layout.push(next(vm));
                    let after = vm.new_block(vm.blocks[block.0].pc);
                    vm.blocks[after.0].instructions.push(ret.clone());
                    layout.extend(Self::protected_call(a, b, 0, after));
                    layout.push(ret);
                    vm.join_effects(owner, Effects::OPAQUE);
                },
                LValue::NClosure(nf) if identities < MAX_VERSIONS => {
                    layout.push(Residual::NativeGuard { idx: a, ptr: nf.get_ptr() });
                    layout.push(next(vm));
                    layout.push(Residual::NativeCall { nf: nf.native(), a: a16, b: b16, c: 0 });
                    // A native may allocate (a table, a string).
                    layout.push(Residual::GC);
                    layout.push(ret);
                    if !nf.is_pure() {
                        vm.join_effects(owner, Effects::OPAQUE);
                    }
                },
                _ => {
                    layout.push(Residual::Call { a: a16, b: b16, c: 0 });
                    layout.push(Residual::Arrive { a: a16, c: 0 });
                    // It may call a native, which may allocate.
                    layout.push(Residual::GC);
                    layout.push(ret);
                    vm.join_effects(owner, Effects::OPAQUE);
                },
            }
            vm.blocks[block.0].instructions.extend(layout);
        })))
    }

    /// The thunk hash key `href`, of register `idx`, is found at. Forced, it finds the key in the
    /// table at the hash key's place and lays out its `href_init` and the guard of its field's
    /// type, continuing the generator with the field known, or, for an `__index`'s hash key, the
    /// thunk of the hash key after it (`next`). A load (`chains`) of a key its table lacks, or has
    /// nil, in a table whose metatable has an `__index` table goes on down the chain; any other key
    /// a load can't find, or a store's table lacks, continues the generator without it, in
    /// `fail_ctx`. See Notes [Field types] and [Table metatables].
    fn make_href_thunk(&self, block_id: BlockId, thunk_coro: Box<Gen>, idx: usize, href: HashRef, pc: SubPc, thunk_ctx: Rc<Context>, appends: bool, chains: bool, next: Option<HashRef>, fail_ctx: Rc<Context>) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            // Each forcing patches the thunk where it was forced, in `block_id`.
            let mut block_id = block_id;
            let thunk_coro = thunk_coro.clone();
            let mut ctx = thunk_ctx.clone();
            let place = ctx.hkeys[href.0 as usize].place;
            debug!("forcing href thunk for {idx} {href:?} {:?}", ctx.hkeys[href.0 as usize]);
            let key = LCanon::new((&ctx.hkeys[href.0 as usize].key).into(), state.intern);
            let tab = state.place_table(owner, idx, place);
            let entry = tab.as_ref().and_then(|tab| tab.ro(owner).hash.get_full(&key).map(|(index, _, val)| (index, *val)));
            let nil = entry.is_none_or(|(_, val)| val.is_nil());
            // A nil field is no field: a load goes on down the chain. See Note [Table
            // metatables].
            let chained = chains && next.is_none() && nil
                && ctx.chain_depth(href) < MAX_CHAIN
                && tab.as_ref().is_some_and(|tab| tab.index_table(owner).is_some());
            // A load never finds nil through a hash key: another table reaching it may
            // have a metatable.
            let usable = match next {
                None if chains => !nil || chained,
                _ => entry.is_some(),
            };
            if !usable {
                let fail_block = vm.new_block(pc.0);
                let compiled = vm.compile_one(owner, pc.next_false(), fail_ctx.clone(), thunk_coro, ResumeArg::Failed, fail_block);
                vm.go_on(owner, compiled, fail_block);
                vm.jump_thunk(block_id, thunk_pc, fail_block);
                return;
            }
            let (index, val) = entry.unwrap_or((0, LBoxed::NIL));
            debug!("href forced by {place:?} -> {val:?}");
            // The field's type in this table, which the guard after `href_init` checks in every
            // table reaching the code. See Note [Field types].
            let found = val.unbox().typeof_();
            let receiver = state.vals[state.base + idx].unbox().typeof_();
            let ctx_mut = Rc::make_mut(&mut ctx);
            {
                let hkey = &mut ctx_mut.hkeys[href.0 as usize];
                hkey.known_type = Some(Kind::Of(found));
                hkey.chain = None;
                // Initialize the hkey after discovery with a cleared hazard for the index
                hkey.clear_checks();
                hkey.check(idx);
            }
            // A chain it had before goes.
            ctx_mut.fix_chains();
            let kbits = LCanon::constant(&ctx_mut.hkeys[href.0 as usize].key).boxed().bits();
            // The receiver's shape now has this hash key.
            if place == Place::Register {
                if let CType::Shape(_, existing) = &mut ctx_mut.types[idx] {
                    if !existing.contains(&href) {
                        existing.push(href)
                    }
                } else {
                    ctx_mut.types[idx] = CType::Shape(receiver, vec![href].into());
                }
            }
            let at = (index as u64) << 8 | href.0 as u64;
            let href_init = Residual::ExecWindow(match (place, receiver) {
                (Place::Register, LType::Table) => Rc::new(HrefInit::new(at, kbits, &[idx])) as Rc<dyn Window>,
                (Place::Register, LType::Userdata) => Rc::new(HrefInitIndex::new(at, kbits, &[idx])),
                (Place::Register, _) => unreachable!("a hash key of a {receiver}"),
                (place, _) => Rc::new(HrefInitAt::new(at, kbits, place.bits(), &[])),
            });
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
            let typed = vm.new_block(pc.0);
            let missing_key = vm.new_block(pc.0);
            vm.blocks[block_id.0].instructions.push(Residual::Select(
                vec![("has_key", typed), ("missing_key", missing_key)]));
            if chained {
                // Its own field is none or nil, which a guard checks where it has the key,
                // and the chain goes on at its metatable's `__index`, then the key in the
                // table that is. See Note [Table metatables].
                let index_key: LConstant<'_, '_> = crate::chunk::Constant::String(crate::vm::intern_bytes(state.intern, b"__index"));
                // As the generator's constants, the intern arena outlives the code.
                let index_key: LConstant<'static, 'static> = unsafe { core::mem::transmute(index_key) };
                let own_key: LConstant<'static, 'static> = unsafe { core::mem::transmute(ctx_mut.hkeys[href.0 as usize].key.clone()) };
                let link = ctx_mut.alloc_hkey(HashKey { place: Place::Metatable(href), known_type: Some(Kind::Mixed), ..HashKey::new(idx, index_key) });
                let found_at = ctx_mut.alloc_hkey(HashKey { place: Place::Index(link), known_type: Some(Kind::Mixed), ..HashKey::new(idx, own_key) });
                ctx_mut.hkeys[href.0 as usize].chain = Some(found_at);
                let chain = vm.new_block(pc.0);
                let link_thunk = vm.make_href_thunk(chain, thunk_coro.clone(), idx, link, pc, ctx.clone(), true, true, Some(found_at), fail_ctx.clone());
                vm.blocks[chain.0].instructions.push(Residual::Thunk(link_thunk));
                let refind = vm.make_href_thunk(typed, thunk_coro.clone(), idx, href, pc, thunk_ctx.clone(), false, chains, None, fail_ctx.clone());
                vm.blocks[typed.0].instructions.push(Residual::GuardWitness { href, expected: LType::Nil });
                vm.blocks[typed.0].instructions.push(Residual::Thunk(refind));
                vm.blocks[typed.0].instructions.push(Residual::Jump(chain));
                vm.blocks[missing_key.0].instructions.push(Residual::Jump(chain));
                return;
            }
            // A table reaching it without the key: found again, down its chain or not at all.
            let refind = vm.make_href_thunk(missing_key, thunk_coro.clone(), idx, href, pc, thunk_ctx.clone(), false, chains, next, fail_ctx.clone());
            vm.blocks[missing_key.0].instructions.push(Residual::Thunk(refind));
            vm.guard_witness(owner, typed, thunk_coro, idx, href, found, pc, ctx, chains, next, fail_ctx.clone());
        })))
    }

    /// End `block` in a `GuardWitness` of `href`'s field for `expected`, its pass continuing the
    /// generator with the field known to be of that type, or, for an `__index`'s hash key, the
    /// thunk of the hash key after it (`next`), and its failure finding the field's type and
    /// guarding that in turn: a load's field found nil, or an `__index` no longer a table, is
    /// found again instead. See Notes [Field types] and [Table metatables].
    fn guard_witness(&mut self, owner: &mut Owner, block: BlockId, thunk_coro: Box<Gen>, idx: usize, href: HashRef, expected: LType, pc: SubPc, ctx: Rc<Context>, chains: bool, next: Option<HashRef>, fail_ctx: Rc<Context>) {
        let mut typed_ctx = ctx.clone();
        Rc::make_mut(&mut typed_ctx).hkeys[href.0 as usize].known_type = Some(Kind::Of(expected));
        let pass = match next {
            Some(next) => {
                let pass = self.new_block(pc.0);
                let thunk = self.make_href_thunk(pass, thunk_coro.clone(), idx, next, pc, typed_ctx, true, true, None, fail_ctx.clone());
                self.blocks[pass.0].instructions.push(Residual::Thunk(thunk));
                pass
            },
            None => self.subblock(owner, pc.next_true(), typed_ctx, thunk_coro.clone(), ResumeArg::HashRef(href, Kind::Of(expected))),
        };
        let fail = ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            let witness = state.hash_witnesses[state.witness_base + href.0 as usize];
            let found = unsafe { *witness.value.cast::<LBoxed<'_, '_>>() }.unbox().typeof_();
            debug!("field of {href:?} found {found}, not {expected}");
            let again = vm.new_block(pc.0);
            vm.jump_thunk(block, thunk_pc, again);
            if (chains && found == LType::Nil) || next.is_some() {
                let refind = vm.make_href_thunk(again, thunk_coro.clone(), idx, href, pc, ctx.clone(), true, chains, next, fail_ctx.clone());
                vm.blocks[again.0].instructions.push(Residual::Thunk(refind));
                return;
            }
            vm.guard_witness(owner, again, thunk_coro.clone(), idx, href, found, pc, ctx.clone(), chains, next, fail_ctx.clone());
        })));
        self.blocks[block.0].instructions.push(Residual::GuardWitness { href, expected });
        self.blocks[block.0].instructions.push(Residual::Thunk(fail));
        self.blocks[block.0].instructions.push(Residual::Jump(pass));
    }

    fn make_epoch_check(&mut self, owner: &mut Owner, block_id: BlockId, thunk_coro: Box<Gen>, tab: usize, href: HashRef, pc: SubPc, thunk_ctx: Rc<Context>, success_block: BlockId, chains: bool) {
        // In order to assert that an href is still valid, we need to check that the witnessed
        // epoch is still the same: if so, all of its keys still have the same type as the
        // cached hashkey, and no additional hashkeys were inserted (which may otherwise cause
        // keys to shadow metatable keys, or resize the hashtable and invalidate pointers).
        // The epoch check block is behind a thunk, because since we dynamically track table
        // epoches in our witness table they only ever would fail if a table transitions its type
        // inside a block, which is unlikely to happen very often.
        let thunk_coro = thunk_coro.clone();
        self.blocks[block_id.0].instructions.push(Residual::EpochCheck { tab, href, place: Place::Register });
        // Build the thunk for if we fail the epoch check
        let fail_thunk = ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            debug!("hit epoch fail thunk");
            // The epoch is different, but the actual key type might still be the same.
            // Do another check for the key type, where if it still holds we can update the
            // witness epoch and jump back to the success block.
            let check_block = vm.new_block(pc.0);
            vm.jump_thunk(block_id, thunk_pc, check_block);
            let expected = thunk_ctx.hkeys[href.0 as usize].known_type.expect("a live hash key");
            let update_href_thunk = vm.make_href_thunk(check_block, thunk_coro.clone(), tab, href.clone(), pc, thunk_ctx.clone(), false, chains, None, thunk_ctx.clone());
            // A field of no stable type has nothing to check it still has: its
            // hash key is found again. See Note [Field types].
            let Kind::Of(expected) = expected else {
                vm.blocks[check_block.0].instructions.push(Residual::Thunk(update_href_thunk));
                return;
            };
            let key = LCanon::constant(&thunk_ctx.hkeys[href.0 as usize].key).boxed().bits();
            vm.blocks[check_block.0].instructions.push(Residual::HashGuard { tab, href: href.clone(), key, expected });
            vm.blocks[check_block.0].instructions.push(Residual::Thunk(update_href_thunk));
            vm.blocks[check_block.0].instructions.push(Residual::Exec(ResidualExec::new("epoch_repair", Rc::new(move |owner, state| {
                // Re-init the witness and jump back to success block
                // The entry may have moved with the epoch: find its value again
                // by its index. See Note [Hash witnesses].
                // The table may be another, which `HashGuard` found the key in.
                let t = state.hash_part_at(owner, tab).expect("a table `HashGuard` found the key in");
                let epoch = t.ro(owner).epoch;
                debug!("repairing {:?} epoch", href);
                let witness = &mut state.hash_witnesses[state.witness_base + href.0 as usize];
                let value = t.rw(owner).hash.get_index_mut(witness.index).unwrap().1 as *mut LBoxed<'_, '_>;
                witness.value = value.cast();
                witness.epoch = epoch;
                witness.table = t.0.to_addr();
            }))));
            vm.blocks[check_block.0].instructions.push(Residual::Jump(success_block));
        })));
        self.blocks[block_id.0].instructions.push(Residual::Thunk(fail_thunk));
    }

    pub fn compile_one(&mut self, owner: &mut Owner, pc: SubPc, ctx: Rc<Context>, coro: Box<Gen>, arg: ResumeArg, block_id: BlockId) -> Compiled
    {
        let continued = self.continued.len();
        let compiled = self.compile_one_of(owner, pc, ctx, coro, arg, block_id);
        self.continued.truncate(continued);
        compiled
    }

    fn compile_one_of(&mut self, owner: &mut Owner, pc: SubPc, ctx: Rc<Context>, coro: Box<Gen>, arg: ResumeArg, block_id: BlockId) -> Compiled
    {
        // Going on in an instruction, not starting it: an exit of what the peephole holds from
        // here goes on from here. See Note [Peephole fusion] in `peephole`.
        if std::mem::take(&mut self.entering) {
            return self.compile_yields(owner, pc, ctx, coro, arg, block_id);
        }
        let holds = self.unheld.take() != Some(pc.0);
        let restart = Restart::Resume(pc, ctx.clone(), coro.clone(), arg.clone());
        let outer = self.instruction.replace((pc.0, restart, holds));
        let compiled = self.compile_yields(owner, pc, ctx, coro, arg, block_id);
        self.instruction = outer;
        compiled
    }

    fn compile_yields(&mut self, owner: &mut Owner, mut pc: SubPc, mut ctx: Rc<Context>, mut coro: Box<Gen>, mut arg: ResumeArg, block_id: BlockId) -> Compiled
    {
        // Where the constant being loaded was, for its fact's origin.
        let mut loading: Option<Origin> = None;
        loop {
            // What the peephole sees of the code it compiles. See Note [Peephole fusion] in
            // `peephole`.
            coro.see(&ctx, self.proto, self.instruction.as_ref().map(|(at, _, holds)| (*at, *holds)));
            let mut state = Pin::new(&mut coro).resume(arg);
            arg = ResumeArg::Start;
            'machine: loop {
            match state {
                CoroutineState::Yielded(YieldOp::TypeofK(k)) => {
                    let proto = self.proto;
                    arg = ResumeArg::Type(constant_ctype(unsafe { &(&(*proto).constants.items)[k] }));
                },
                CoroutineState::Yielded(YieldOp::IntegerK(k)) => {
                    let proto = self.proto;
                    let crate::chunk::Constant::Number(n) = (unsafe { &(&(*proto).constants.items)[k] }) else { unreachable!() };
                    assert!(is_integer(n.0), "{} isn't an integer", n.0);
                    arg = ResumeArg::Integer(n.0 as i32);
                },
                CoroutineState::Yielded(YieldOp::IntegralK(k)) => {
                    let proto = self.proto;
                    arg = if integral_constant(unsafe { &(&(*proto).constants.items)[k] }) { ResumeArg::Matched } else { ResumeArg::Failed };
                },
                CoroutineState::Yielded(YieldOp::NumberK(k)) => {
                    let proto = self.proto;
                    let crate::chunk::Constant::Number(n) = (unsafe { &(&(*proto).constants.items)[k] }) else { unreachable!() };
                    // Its NaN canonicalized, as boxing it would.
                    // See Note [Arithmetic NaNs].
                    arg = ResumeArg::Number(if n.0.is_nan() { f64::NAN } else { n.0 });
                },
                CoroutineState::Yielded(YieldOp::BoxedK(k)) => {
                    let proto = self.proto;
                    arg = ResumeArg::Boxed(LBoxed::from(unsafe { &(&(*proto).constants.items)[k] }).bits());
                },
                op @ CoroutineState::Yielded(YieldOp::Typeof(idx) | YieldOp::TypeofRk(idx)) => {
                    if let CoroutineState::Yielded(YieldOp::TypeofRk(key)) = op {
                        let proto = self.proto;
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
                    // A store of a value of unknown type keeps the field's old type:
                    // there's a chance the unknown static type is in fact still our old
                    // type and we just didn't know, and if there is a runtime mismatch
                    // the next access's epoch check and `HashGuard` find it, as the store
                    // left the witness at the old epoch (`Retype::Unknown`).
                    let hkey = &mut Rc::make_mut(&mut ctx).hkeys[href.0 as usize];
                    if let Some(ty) = *ty {
                        hkey.known_type = Some(Kind::Of(ty));
                    }
                    // If we updated an href, then we also need to set optimization hazards for any
                    // potentially aliased ones. We also need to invalidate this stack slot as
                    // well.
                    state = CoroutineState::Yielded(YieldOp::SetHazards(None, Some(href)));
                    arg = ResumeArg::Failed;
                    continue 'machine;
                },
                CoroutineState::Yielded(YieldOp::IsKey(k, name)) => {
                    let proto = self.proto;
                    let constant = unsafe { &(&(*proto).constants.items)[k] };
                    arg = if matches!(constant, crate::chunk::Constant::String(s) if s.as_bytes() == name) { ResumeArg::Matched } else { ResumeArg::Failed };
                },
                CoroutineState::Yielded(ref yielded @ (YieldOp::HashKey(..) | YieldOp::HashKeyNamed(..))) => {
                    let proto = self.proto;
                    // The key: a constant, or one known by its value.
                    let (place, chains, named) = match yielded {
                        YieldOp::HashKey(place, key, chains) => (*place, *chains, ((key & 0x100) != 0).then(|| unsafe { (&(*proto).constants.items)[key & 0xff].clone() })),
                        YieldOp::HashKeyNamed(place, key, chains) => (*place, *chains, Some(key.clone())),
                        _ => unreachable!(),
                    };
                    // Only cache string keys
                    let Some(k_val) = named.as_ref().filter(|k_val| matches!(k_val, crate::chunk::Constant::String(_)))
                    else {
                        pc = pc.next_false();
                        arg = ResumeArg::Failed;
                        break 'machine;
                    };
                    // The table's existing hash keys: its shape's.
                    let existing: SmallVec<[HashRef; 4]> = match &ctx.types[place] {
                        CType::Type(LType::Table | LType::Userdata) => SmallVec::new(),
                        CType::Shape(_, existing) => existing.clone(),
                        _ => panic!("HashKey should only be used on a table or a userdata"),
                    };
                    debug!("hashkey on existing {existing:?}");
                    if let Some(cached) = existing.into_iter().find(|cached| &ctx.hkeys[cached.0 as usize].key == k_val) {
                        debug!("using cached href {:?}", cached);
                        let chain = ctx.chain_of(cached);
                        let tail = *chain.last().unwrap();
                        let tail_type = ctx.hkeys[tail.0 as usize].known_type.expect("a live hash key");
                        // A store sets the register's own field, never one down its
                        // chain. See Note [Table metatables].
                        if !chains && chain.len() > 1 {
                            pc = pc.next_false();
                            arg = ResumeArg::Failed;
                            break 'machine;
                        }
                        // A load never finds nil, or a field of no stable type, through a
                        // hash key: it finds it again, down the chain or not at all.
                        if chains && !matches!(tail_type, Kind::Of(t) if t != LType::Nil) {
                            let refind = self.make_href_thunk(block_id, coro.clone(), place, cached, pc, ctx.clone(), true, true, None, ctx.clone());
                            self.end_block(block_id);
                            self.blocks[block_id.0].instructions.push(Residual::Thunk(refind));
                            return None;
                        }
                        // A cached href. Unless nothing could have invalidated it
                        // since it was last checked, it needs an epoch check first,
                        // which continues into blocks assuming it still holds; a
                        // chain's, every one of its hash keys'.
                        arg = ResumeArg::HashRef(tail, tail_type);
                        if chain.iter().all(|h| ctx.hkeys[h.0 as usize].checked(place)) {
                            // Nothing could have invalidated it: no check needed.
                            pc = pc.next_true();
                            debug!("using cached hkey without hazards");
                            break 'machine;
                        }
                        // After a passing epoch check, later accesses need no check
                        // until something may invalidate it again.
                        let mut holds_ctx = ctx.clone();
                        for h in &chain {
                            Rc::make_mut(&mut holds_ctx).hkeys[h.0 as usize].check(place);
                        }
                        let holds_block = self.subblock(owner, pc.next_true(), holds_ctx.clone(), coro.clone(), arg);
                        if chain.len() == 1 {
                            self.make_epoch_check(owner, block_id, coro.clone(), place, cached.clone(), pc, ctx.clone(), holds_block, chains);
                        } else {
                            // Each in turn, each one's table found through the ones before it;
                            // any failing finds the key again. See Note [Table metatables].
                            for &h in &chain {
                                let refind = self.make_href_thunk(block_id, coro.clone(), place, cached, pc, ctx.clone(), false, true, None, ctx.clone());
                                self.blocks[block_id.0].instructions.push(Residual::EpochCheck { tab: place, href: h, place: ctx.hkeys[h.0 as usize].place });
                                self.blocks[block_id.0].instructions.push(Residual::Thunk(refind));
                            }
                        }

                        self.end_block(block_id);
                        self.blocks[block_id.0].instructions.push(Residual::Jump(holds_block));
                        return None;
                    }
                    // We need these HashKeys to not have a lifetime, so that they can be
                    // captured by the generator: we only ever store the generator in the
                    // LClosure they came from, which is 'src 'lifetime, and so this is safe.
                    let k_val: &LConstant<'static, 'static> = unsafe { core::mem::transmute(k_val) };
                    // At the field's index for its slot, which every path through the code
                    // gives it, if no other hash key is there; else at a free one, or a new one.
                    // See Note [Field types].
                    let href;
                    let fixed = self.key_index(&ctx, place, k_val);
                    let orphan = ctx.hkeys.iter().enumerate().position(|(_, hkey)| hkey.orphan());
                    if let Some(i) = fixed.filter(|&i| ctx.hkeys.get(i).is_none_or(|hkey| hkey.orphan())) {
                        href = HashRef(i as u8);
                        let ctx = Rc::make_mut(&mut ctx);
                        while ctx.hkeys.len() <= i {
                            ctx.hkeys.push(HashKey { idx: OUTER, ..HashKey::new(OUTER, k_val.clone()) });
                        }
                        ctx.hkeys[i] = HashKey::new(place, k_val.clone());
                    } else if let Some(i) = orphan {
                        href = HashRef(i as u8);
                        let ctx = Rc::make_mut(&mut ctx);
                        ctx.hkeys[i] = HashKey::new(place, k_val.clone());
                    } else {
                        warn!("allocating new hkey for {:?} {:?}", place, &k_val);
                        let hr: u8 = ctx.hkeys.len().try_into().expect("too many hrefs");
                        href = HashRef(hr);
                        let hkey = HashKey::new(place, k_val.clone());
                        #[cfg(debug_assertions)]
                        assert_eq!(ctx.hkeys.iter().filter(|exist| **exist == hkey).next(), None);
                        Rc::make_mut(&mut ctx).hkeys.push(hkey);
                    }
                    let thunk_coro = coro.clone();
                    let thunk_ctx = ctx.clone();
                    let witness = Residual::Thunk(self.make_href_thunk(block_id, thunk_coro, place, href.clone(), pc, thunk_ctx.clone(), true, chains, None, thunk_ctx));
                    self.end_block(block_id);
                    self.blocks[block_id.0].instructions.push(witness);
                    return None;
                },
                CoroutineState::Yielded(YieldOp::GuardRk(rk, ref expected)) => {
                    let proto = self.proto;
                    if (rk & 0x100)!=0 {
                        let r_const = rk & (0xff);
                        let ty = constant_ctype_for(unsafe { &(&(*proto).constants.items)[r_const as usize] }, &CType::Type(*expected));
                        debug!("GuardRk constant {:?} {:?}", ty, expected);
                        // Constants always have known types
                        if CType::Type(*expected).accepts(&ty) {
                            pc = pc.next_true();
                            arg = ResumeArg::MatchedConst(r_const);
                        } else {
                            pc = pc.next_false();
                            arg = ResumeArg::Failed;
                        }
                        break 'machine;
                    } else {
                        debug!("GuardRk dynamic {:?} {:?}", rk, expected);
                        state = CoroutineState::Yielded(YieldOp::Guard(rk as usize, expected.clone()));
                        continue 'machine;
                    }
                },
                CoroutineState::Yielded(YieldOp::GuardCType(rk, ref expected)) => {
                    let known = if (rk & 0x100) != 0 {
                        let proto = self.proto;
                        constant_ctype_for(unsafe { &(&(*proto).constants.items)[rk & 0xff] }, expected)
                    } else {
                        ctx.types[rk].clone()
                    };
                    // Known if `known` is `expected` or below it, or can't be: else
                    // found out at runtime.
                    if expected.accepts(&known) || !known.accepts(expected) {
                        (pc, arg) = navigate(pc, expected, &known);
                        if (rk & 0x100) != 0 && arg == ResumeArg::Matched {
                            arg = ResumeArg::MatchedConst(rk & 0xff);
                        }
                    } else {
                        // See Note [Widening].
                        Rc::make_mut(&mut ctx).used(rk);
                        let thunk = Residual::Thunk(self.make_discovery_thunk(block_id, coro.clone(), rk, expected.clone(), None, pc, ctx.clone(), true, 0));
                        self.end_block(block_id);
                        self.blocks[block_id.0].instructions.push(thunk);
                        return None;
                    }
                },
                CoroutineState::Yielded(YieldOp::Encoding(_)) if let Some(how) = self.decision(owner, pc) => {
                    arg = how;
                },
                // An integer op while the peephole holds: as it fits. See Note [Peephole fusion].
                CoroutineState::Yielded(YieldOp::Encoding(_)) if coro.holds_any() => {
                    arg = ResumeArg::Type(CType::Type(LType::Integer));
                },
                CoroutineState::Yielded(YieldOp::Encoding(fits)) => {
                    // Decided by its operands the first time it runs. See Note [Optimistic ops].
                    let thunk = Residual::Thunk(self.make_encoding_thunk(block_id, coro.clone(), pc, ctx.clone(), fits));
                    self.end_block(block_id);
                    self.blocks[block_id.0].instructions.push(thunk);
                    return None;
                },
                // An integer op the peephole holds: what laying it out would do to what the context
                // knows. See Note [Peephole fusion] in `peephole`.
                CoroutineState::Yielded(YieldOp::Holding { writes, reads, constant, optimistic }) => {
                    let loaded = reads.iter().any(|&slot| matches!(ctx.values.fact(Loc::root(Root::Slot(slot as u16)), CONSTANT), Some(Known::Constant { origins: Some(_), .. })));
                    for slot in writes {
                        Rc::make_mut(&mut ctx).effect(Effect::Write(slot));
                    }
                    if let Some((dest, value)) = constant && !loaded {
                        Rc::make_mut(&mut ctx).values.learn(Loc::root(Root::Slot(dest as u16)), Known::Constant { value, origins: None });
                    }
                    // Its encoding was asked of the peephole, not decided. See Note [Optimistic ops].
                    if optimistic {
                        self.encoding = None;
                        pc = pc.next_true();
                    }
                },
                // What the peephole holds, laid out: an op that can fail, whose cold way is an exit
                // writing what is still unwritten, from the instruction's restart. The code goes on
                // past it, the peephole holding what it holds still.
                CoroutineState::Yielded(YieldOp::Fused { op, exit, unknown }) => {
                    let (at, restart, _) = self.instruction.clone().expect("spells are held in an instruction");
                    self.end_block(block_id);
                    self.blocks[block_id.0].instructions.push(Residual::ExecWindow(op));
                    let cold = self.new_block(pc.0);
                    let exit = self.make_held_exit(cold, exit, unknown, at, restart);
                    self.blocks[cold.0].instructions.push(Residual::Thunk(exit));
                    let hot = self.new_block(pc.0);
                    self.blocks[block_id.0].instructions.push(Residual::Branch { hot, cold });
                    self.entering = true;
                    let compiled = self.compile_one(owner, pc, ctx, coro, ResumeArg::Matched, hot);
                    self.go_on(owner, compiled, hot);
                    return None;
                },
                // A guard the peephole joined to a spell: as passed.
                CoroutineState::Yielded(YieldOp::Took) => {
                    pc = pc.next_true();
                },
                CoroutineState::Yielded(YieldOp::LayOut) => {},
                CoroutineState::Yielded(YieldOp::Created(slot)) => {
                    Rc::make_mut(&mut ctx).values.learn(Loc::root(Root::Slot(slot as u16)), Known::Unwatched);
                },
                CoroutineState::Yielded(YieldOp::LaidOut(w)) => {
                    self.blocks[block_id.0].instructions.push(Residual::ExecWindow(w));
                },
                // The base moved to the frames of the inlined calls the code is in, before code naming
                // their slots, making none of them. See Note [Peephole fusion] in `peephole`.
                CoroutineState::Yielded(YieldOp::Enter) => {
                    // Each frame's slots past its arguments are nil as the peephole holds them unset,
                    // a nil laid out for each only where read. See Note [Peephole memory] in
                    // `peephole`.
                    let entered = Rc::make_mut(&mut ctx);
                    for frame in entered.inline.iter_mut().filter(|frame| frame.made == Made::No) {
                        frame.made = Made::Base;
                        self.blocks[block_id.0].instructions.push(Residual::Enter(frame.by() as u16));
                    }
                    if let Some((_, restart, _)) = &mut self.instruction {
                        restart.made_as(&ctx);
                    }
                },
                // Their frames made, before code observing them: the code goes on inside them, in a
                // block of its own, as a call's code goes on.
                CoroutineState::Yielded(YieldOp::MakeFrames) => {
                    let (inside, made) = self.make_frames(block_id, pc.0, &ctx);
                    if let Some((_, restart, _)) = &mut self.instruction {
                        restart.made_as(&made);
                    }
                    self.entering = true;
                    let compiled = self.compile_one(owner, pc, made, coro, ResumeArg::Start, inside);
                    self.go_on(owner, compiled, inside);
                    return None;
                },
                CoroutineState::Yielded(YieldOp::IntegerOp(_) | YieldOp::MemoryOp(_) | YieldOp::HoldsValue(..) | YieldOp::FrameUnmade) => unreachable!("the peephole takes what describes an op, or asks of what it holds"),
                CoroutineState::Yielded(YieldOp::PeepholeTrace(_name, _fields)) => {
                    #[cfg(feature = "tracing")]
                    {
                        let mut args: Vec<(&str, crate::tracing::TraceValue)> = vec![
                            ("line", self.traced_line(owner).into()),
                            ("pc", (pc.0 as u64).into()),
                            ("block", (block_id.0 as u64).into()),
                        ];
                        args.extend(_fields.iter().map(|(key, value)| (*key, value.as_str().into())));
                        crate::tracing::instant("peephole", _name, &args);
                    }
                },
                CoroutineState::Yielded(YieldOp::OptimisticExec(op)) => {
                    // Its outputs are written whichever path it takes. See Note [Optimistic ops].
                    for (&slot, access) in op.operands().iter().zip(op.accesses()) {
                        if access.writes() {
                            Rc::make_mut(&mut ctx).effect(Effect::Write(slot));
                        }
                    }
                    self.end_block(block_id);
                    self.blocks[block_id.0].instructions.push(Residual::ExecWindow(op));
                    let hot = self.subblock(owner, pc.next_true(), ctx.clone(), coro.clone(), ResumeArg::Matched);
                    let cold = self.new_block(pc.0);
                    // Its overflow rebuilds it from where its encoding was asked. See Note
                    // [Optimistic ops].
                    let asked = self.encoding.take();
                    let side = self.make_overflow_thunk(cold, coro.clone(), pc.next_false(), ctx.clone(), asked);
                    self.blocks[cold.0].instructions.push(Residual::Thunk(side));
                    self.blocks[block_id.0].instructions.push(Residual::Branch { hot, cold });
                    return None;
                },
                CoroutineState::Yielded(YieldOp::NativeWindowArgs(a, b, c)) => {
                    arg = match native_window(&ctx, a, b, c) {
                        Some((end, op)) => ResumeArg::WindowArgs(end, op.args.clone()),
                        None => ResumeArg::Failed,
                    };
                },
                CoroutineState::Yielded(YieldOp::Decided(passed)) => {
                    (pc, arg) = if passed { (pc.next_true(), ResumeArg::Matched) } else { (pc.next_false(), ResumeArg::Failed) };
                },
                CoroutineState::Yielded(YieldOp::Promote(slot)) => match ctx.constant(slot) {
                    Some(value) if self.promotes(pc.0, value) => {
                        ctx.rely(owner, slot);
                        Rc::make_mut(&mut ctx).promote(pc.0, value);
                        pc = pc.next_true();
                        arg = ResumeArg::Integer(value);
                    }
                    Some(_) => {
                        pc = pc.next_false();
                        arg = ResumeArg::Failed;
                    }
                    None if self.promoted.get(&(self.proto, pc.0)).is_some_and(|values| values.len() >= PROMOTE_SITE_VALUES) => {
                        pc = pc.next_false();
                        arg = ResumeArg::Failed;
                    }
                    None => {
                        let thunk = Residual::Thunk(self.make_promote_thunk(block_id, coro.clone(), slot, pc, ctx.clone()));
                        self.end_block(block_id);
                        self.blocks[block_id.0].instructions.push(thunk);
                        return None;
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
                CoroutineState::Yielded(YieldOp::Watching(slot, _)) if ctx.values.fact(Loc::root(Root::Slot(slot as u16)), WATCHED).is_some() => {
                    pc = pc.next_true();
                    arg = ResumeArg::Matched;
                },
                CoroutineState::Yielded(YieldOp::Watching(slot, freezes)) => {
                    if freezes {
                        Rc::make_mut(&mut ctx).effect(Effect::Watch);
                        // See Note [Call effects].
                        self.join_effects(owner, Effects::WATCH);
                    }
                    let thunk = self.make_watch_thunk(block_id, coro.clone(), slot, pc, ctx.clone(), true, freezes);
                    self.end_block(block_id);
                    self.blocks[block_id.0].instructions.push(Residual::Thunk(thunk));
                    return None;
                },
                CoroutineState::Yielded(YieldOp::FrozenElement(table, key)) => {
                    arg = self.frozen_element(owner, &ctx, table, key).unwrap_or(ResumeArg::Failed);
                },
                CoroutineState::Yielded(YieldOp::Discovered(slot, bits, ctype, constant)) => {
                    let ctx = Rc::make_mut(&mut ctx);
                    ctx.set_types(owner, vec![(slot, ctype)]);
                    let at = Loc::root(Root::Slot(slot as u16));
                    if let Some(value) = constant {
                        ctx.values.learn(at, Known::Constant { value, origins: None });
                    }
                    ctx.values.learn(at, Known::Value(bits));
                },
                CoroutineState::Yielded(YieldOp::Uniques(of)) => {
                    let theirs = |roots: &Vec<Root>| roots.iter().any(|root| of.iter().any(|&slot| *root == Root::Slot(slot as u16)));
                    let slots: Option<Vec<usize>> = ctx.values.knowing(UNIQUE).iter().filter(|roots| !theirs(roots))
                        .map(|roots| roots.iter().find_map(|root| match root { Root::Slot(slot) => Some(*slot as usize), _ => None }))
                        .collect();
                    arg = slots.map_or(ResumeArg::Failed, |slots| ResumeArg::Slots(slots.into()));
                },
                CoroutineState::Yielded(YieldOp::Unique(slots)) => {
                    let ctx = Rc::make_mut(&mut ctx);
                    for slot in slots {
                        ctx.values.learn(Loc::root(Root::Slot(slot as u16)), Known::Unique);
                    }
                },
                CoroutineState::Yielded(YieldOp::ValueOf(slot)) => {
                    arg = match ctx.values.fact(Loc::root(Root::Slot(slot as u16)), VALUE) {
                        Some(&Known::Value(bits)) => ResumeArg::Boxed(bits),
                        _ => ResumeArg::Failed,
                    };
                },
                // A table known unwatched is checked no more. See Note [Watched tables].
                CoroutineState::Yielded(YieldOp::Trip(Some(slot))) if ctx.values.fact(Loc::root(Root::Slot(slot as u16)), UNWATCHED).is_some() => {
                    pc = pc.next_true();
                    arg = ResumeArg::Matched;
                },
                CoroutineState::Yielded(YieldOp::Trip(of)) => {
                    // Its cold way, the table watched, goes on knowing no element. See Note
                    // [Watched tables].
                    let check: Rc<dyn Window> = match of {
                        Some(slot) => Rc::new(TripCheck::new(&[slot])),
                        None => Rc::new(TripCheckGlobal::new(&[])),
                    };
                    self.end_block(block_id);
                    self.blocks[block_id.0].instructions.push(Residual::ExecWindow(check));
                    let mut passed = (*ctx).clone();
                    if let Some(slot) = of {
                        passed.values.learn(Loc::root(Root::Slot(slot as u16)), Known::Unwatched);
                    }
                    let hot = self.subblock(owner, pc.next_true(), Rc::new(passed), coro.clone(), ResumeArg::Matched);
                    let cold = self.new_block(pc.0);
                    let mut unwatched = (*ctx).clone();
                    unwatched.effect(Effect::Trip);
                    let side = self.make_side_thunk(cold, coro.clone(), pc.next_false(), Rc::new(unwatched), ResumeArg::Matched);
                    self.blocks[cold.0].instructions.extend([Residual::Tripped(of), Residual::Thunk(side)]);
                    self.blocks[block_id.0].instructions.push(Residual::Branch { hot, cold });
                    return None;
                },
                CoroutineState::Yielded(YieldOp::Learn(slot)) => {
                    let thunk = self.make_learn_thunk(block_id, coro.clone(), slot, pc, ctx.clone());
                    self.end_block(block_id);
                    self.blocks[block_id.0].instructions.push(Residual::Thunk(thunk));
                    return None;
                },
                CoroutineState::Yielded(YieldOp::LearnKind(slot)) => {
                    if ctx.kind(Root::Slot(slot as u16)).is_some() {
                        pc = pc.next_true();
                        arg = ResumeArg::Matched;
                    } else {
                        let thunk = self.make_learn_kind_thunk(block_id, coro.clone(), slot, pc, ctx.clone());
                        self.end_block(block_id);
                        self.blocks[block_id.0].instructions.push(Residual::Thunk(thunk));
                        return None;
                    }
                },
                CoroutineState::Yielded(YieldOp::Guard(idx, expected)) => {
                    debug!("guard {:?} == {:?}", ctx.types[idx], expected);
                    let ctype = &ctx.types[idx];
                    let expected_ctype = CType::Type(expected);

                    if expected_ctype.accepts(ctype) {
                        // Statically true: pump the success path
                        pc = pc.next_true();
                        arg = ResumeArg::Matched;
                    }
                    else if !ctype.accepts(&expected_ctype) {
                        // Statically false: pump the fail path
                        pc = pc.next_false();
                        arg = ResumeArg::Failed;
                    } else {
                        // Dynamic branch: create a thunk that will discovery the type of the
                        // guarded value when forced, and fork the coroutine for the observed case.
                        // See Note [Widening].
                        Rc::make_mut(&mut ctx).used(idx);
                        let thunk_coro = coro.clone();
                        let thunk_ctx = ctx.clone();
                        debug!("emitting discovery thunk");
                        // What the peephole holds, the guard's ways hold too. See Note [Peephole
                        // fusion] in `peephole`.
                        let thunk = Residual::Thunk(self.make_discovery_thunk(block_id, thunk_coro, idx, CType::Type(expected), None, pc, thunk_ctx, true, 0));
                        self.end_block(block_id);
                        self.blocks[block_id.0].instructions.push(thunk);
                        return None;
                    }
                }
                CoroutineState::Yielded(YieldOp::Exec(func)) => {
                    match &func.writes {
                        Some(slots) => for &slot in slots {
                            Rc::make_mut(&mut ctx).effect(Effect::Write(slot));
                        },
                        None => Rc::make_mut(&mut ctx).effect(Effect::WriteAny),
                    }
                    self.blocks[block_id.0].instructions.push(Residual::Exec(func));
                },
                CoroutineState::Yielded(YieldOp::ExecWindow(w)) => {
                    for (&slot, access) in w.operands().iter().zip(w.accesses()) {
                        if access.writes() {
                            Rc::make_mut(&mut ctx).effect(Effect::Write(slot));
                        }
                    }
                    self.blocks[block_id.0].instructions.push(Residual::ExecWindow(w));
                },
                CoroutineState::Yielded(YieldOp::NativeCall { nf, a, b, c }) => {
                    self.blocks[block_id.0].instructions.push(Residual::NativeCall { nf, a: a as u16, b: b as u16, c: c as u16 });
                    // A native may allocate (a table, a string).
                    self.blocks[block_id.0].allocates = true;
                    // Its results, and its frame above them, overwrote every register from `a` on.
                    let clobbered: Vec<(usize, CType)> = (a..ctx.types.len()).map(|idx| (idx, CType::Unknown)).collect();
                    for &(idx, _) in &clobbered {
                        Rc::make_mut(&mut ctx).effect(Effect::Write(idx));
                    }
                    Rc::make_mut(&mut ctx).set_types(owner, clobbered);
                    Rc::make_mut(&mut ctx).top = None;
                },
                CoroutineState::Yielded(YieldOp::Captures(closure, upvalues)) => {
                    // See Note [Upvalue paths].
                    let ctx = Rc::make_mut(&mut ctx);
                    for (n, (from, index)) in upvalues.into_iter().enumerate() {
                        let at = Loc::root(Root::Slot(closure as u16));
                        if from == Opcode::MOVE {
                            ctx.values.alias(at, Label::Upvalue(n as u8), index as u16);
                        } else {
                            ctx.values.link(at, Label::Upvalue(n as u8), Loc::root(Root::Upvalue(index as u8)));
                        }
                    }
                },
                CoroutineState::Yielded(YieldOp::Close(from)) => {
                    let ctx = Rc::make_mut(&mut ctx);
                    ctx.values = ctx.closing(from);
                },
                CoroutineState::Yielded(YieldOp::Copy(dest, src)) => {
                    // A copy's class tells more than its slots' type only of a value that can
                    // have fields or a kind, or is a known constant. See Note [Value classes] in
                    // `classes`.
                    let plain = matches!(ctx.slot(src), CType::Number | CType::Type(LType::Nil | LType::Bool | LType::String | LType::Integer | LType::Double));
                    if dest != src && (!plain || ctx.constant(src).is_some()) {
                        Rc::make_mut(&mut ctx).values.assign(Root::Slot(dest as u16), Loc::root(Root::Slot(src as u16)));
                    }
                    // A copy of a table is checked where the table is.
                    if dest != src {
                        for hkey in &mut Rc::make_mut(&mut ctx).hkeys {
                            if hkey.checked(src) {
                                hkey.check(dest);
                            } else if let Some(checked) = hkey.hazards.get_mut(dest) {
                                *checked = false;
                            }
                        }
                    }
                },
                CoroutineState::Yielded(YieldOp::UpvalueHolds(upvalue, slot)) => {
                    // See Note [Upvalue paths].
                    let ctx = Rc::make_mut(&mut ctx);
                    let at = Loc::root(Root::Upvalue(upvalue as u8));
                    ctx.values.assign(Root::Upvalue(upvalue as u8), Loc::root(Root::Slot(slot as u16)));
                    if let Some(ctype) = ctx.value_type(slot) {
                        ctx.values.learn(at, Known::Type(ctype));
                    }
                },
                CoroutineState::Yielded(YieldOp::Effect(effect)) => {
                    Rc::make_mut(&mut ctx).effect(effect);
                    // See Note [Call effects].
                    self.join_effects(owner, Effects::of(effect));
                },
                CoroutineState::Yielded(YieldOp::ArrayKind(table)) => {
                    arg = match ctx.array_kind(table) {
                        Some(kind) => ResumeArg::Type(kind.ctype()),
                        None => ResumeArg::Failed,
                    };
                },
                CoroutineState::Yielded(YieldOp::IsElementOf(slot, table)) => {
                    // The table in slot `table`, wherever else it is.
                    let path = [Label::ElementOf];
                    let loaded = ctx.values.same(Loc { root: Root::Slot(slot as u16), path: &path }, Loc::root(Root::Slot(table as u16)));
                    arg = if loaded { ResumeArg::Matched } else { ResumeArg::Failed };
                },
                // The running closure's own upvalue, which a guard can read the table of;
                // through the slot, a kind found out is the upvalue's too (`learn_kind`).
                CoroutineState::Yielded(YieldOp::Subject(slot)) => {
                    arg = ResumeArg::Subject(ctx.holds(slot).map_or(Root::Slot(slot as u16), Root::Upvalue));
                },
                CoroutineState::Yielded(YieldOp::ArrayType(slot, table)) => {
                    let kind = ctx.kind(table);
                    let ctx = Rc::make_mut(&mut ctx);
                    ctx.set_types(owner, vec![(slot, kind.map_or(CType::Unknown, Kind::ctype))]);
                    // A load into its table's slot has overwritten the table there.
                    if kind.is_none() && table != Root::Slot(slot as u16) {
                        ctx.values.link(Loc::root(Root::Slot(slot as u16)), Label::ElementOf, Loc::root(table));
                    }
                },
                CoroutineState::Yielded(YieldOp::FieldType(slot, href)) => {
                    let known = ctx.hkeys[href.0 as usize].known_type.expect("a live hash key");
                    // A nil field's load is its `__index`'s, of any type. See Note [Table
                    // metatables].
                    let known = match known {
                        Kind::Of(LType::Nil) => Kind::Mixed,
                        known => known,
                    };
                    Rc::make_mut(&mut ctx).set_types(owner, vec![(slot, known.ctype())]);
                    // The slot holds the field's value, and the field's array kind is its. See
                    // Note [Field facts].
                    // Only for a value that can be a table or a function: what a slot holding any
                    // other learns, its type tells already.
                    let object = matches!(known, Kind::Mixed | Kind::Of(LType::Table | LType::Userdata | LType::Closure));
                    if object && let Some((table, name)) = ctx.field_of(href) {
                        Rc::make_mut(&mut ctx).loaded(slot, Root::Slot(table), &[Label::Field(name)]);
                    }
                    if let Kind::Of(known) = known {
                        (pc, arg) = navigate(pc, &CType::Unknown, &CType::Type(known));
                    } else {
                        // Record the type on the hash key too, unless the load overwrote
                        // the table's register and dropped its hash keys.
                        let live = ctx.types.iter().any(|ctype| matches!(ctype, CType::Shape(_, hrefs) if hrefs.contains(&href)));
                        let thunk = Residual::Thunk(self.make_discovery_thunk(block_id, coro.clone(), slot, CType::Unknown, live.then_some(href), pc, ctx.clone(), true, 0));
                        self.end_block(block_id);
                        self.blocks[block_id.0].instructions.push(thunk);
                        return None;
                    }
                },
                CoroutineState::Yielded(YieldOp::UpvalueKnown(upvalue)) => {
                    // A native's fact is of its code, and its value is the one cell it was
                    // made with. A Lua function's is only of its prototype (what its
                    // identity guard compares), which closure isn't known: that, like any
                    // other value, is only known as what a slot still holds.
                    arg = match (ctx.upvalue(upvalue), ctx.held(upvalue)) {
                        (Some(CType::NativeFunction(nf)), _) => ResumeArg::Boxed(LBoxed::box_lvalue(LValue::NClosure(*nf)).bits()),
                        (_, Some(slot)) => ResumeArg::Integer(slot as i32),
                        _ => ResumeArg::Failed,
                    };
                },
                CoroutineState::Yielded(YieldOp::UpvalueCell(upvalue)) => {
                    arg = match ctx.upvalue_cell(upvalue) {
                        Some(cell) => ResumeArg::Cell(cell, ctx.cell_filled(upvalue)),
                        None => ResumeArg::Failed,
                    };
                },
                CoroutineState::Yielded(YieldOp::LoadUpvalue(slot, upvalue)) => {
                    // See Note [Fragile information].
                    let known = ctx.upvalue(upvalue).cloned();
                    // What the context assumes the slot holds: debug builds check it does. See
                    // Note [Fragile information].
                    #[cfg(debug_assertions)]
                    match &known {
                        Some(CType::NativeFunction(nf)) => {
                            windowed!(CheckNative, [native: usize], [], |owner, state, base| (value) {
                                let LValue::NClosure(nf) = value.unbox() else { panic!("fragile information: a native was assumed, {:?} found", value) };
                                assert_eq!(nf.get_ptr() as usize, native, "fragile information: another native was assumed");
                            });
                            self.blocks[block_id.0].instructions.push(Residual::ExecWindow(Rc::new(CheckNative::new(nf.get_ptr() as usize, &[slot]))));
                        },
                        Some(CType::LuaFunction(lclos)) => {
                            windowed!(reads CheckLua, [proto: usize], [], |owner, state, base| (value) {
                                let LValue::LClosure(clos) = value.unbox() else { panic!("fragile information: a Lua function was assumed, {:?} found", value) };
                                assert_eq!(clos.ro(owner).prototype as usize, proto, "fragile information: another Lua function was assumed");
                            });
                            let proto = lclos.ro(owner).prototype as usize;
                            self.blocks[block_id.0].instructions.push(Residual::ExecWindow(Rc::new(CheckLua::new(proto, &[slot]))));
                        },
                        Some(CType::Type(ty)) => {
                            windowed!(CheckType, [ty: LType], [], |owner, state, base| (value) {
                                assert_eq!(value.unbox().typeof_(), ty, "fragile information: another type was assumed");
                            });
                            self.blocks[block_id.0].instructions.push(Residual::ExecWindow(Rc::new(CheckType::new(*ty, &[slot]))));
                        },
                        _ => {},
                    }
                    let ctx = Rc::make_mut(&mut ctx);
                    ctx.set_types(owner, vec![(slot, known.unwrap_or(CType::Unknown))]);
                    // The slot holds the upvalue's value, and what is known of it. See Note
                    // [Upvalue paths].
                    ctx.values.assign(Root::Slot(slot as u16), Loc::root(Root::Upvalue(upvalue as u8)));
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
                CoroutineState::Yielded(op @ (YieldOp::Call(_) | YieldOp::CallResume(_))) => {
                    let (target, resumes) = match op {
                        YieldOp::Call(target) => (target, false),
                        YieldOp::CallResume(target) => (target, true),
                        _ => unreachable!(),
                    };
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
                            // The result's type, if known. A window op's has one; it and a pure
                            // native's call have no effects. See Note [Library natives].
                            let mut result = None;
                            let mut pure = false;
                            let calling = ctx.clone();
                            // A protected call's is laid out by the call thunk, which
                            // needs a continuation for it to unwind to. See Note [Errors].
                            let native = matches!(&ctx.types[a], CType::NativeFunction(nf) if !nf.is_protected_call());
                            // A native with a generator is compiled by it, as an opcode is. See Note
                            // [Native generators] in `library`.
                            if native && !resumes && let CType::NativeFunction(nf) = &ctx.types[a] && let Some(generator) = nf.generator() {
                                coro.generate(generator(nf.native(), a, b, c));
                                arg = ResumeArg::Start;
                                break 'machine;
                            }
                            if native && let CType::NativeFunction(nf) = &ctx.types[a] {
                                // A native runs as a window op if we have one, and we have all of its
                                // arguments of the type it assumes. It gives one result, even with
                                // C = 0.
                                // See Note [Native windows].
                                let window = native_window(&ctx, a, b, c)
                                    .filter(|(end, op)| (a + 1..*end).all(|slot| op.args.accepts(&ctx.types[slot])))
                                    .map(|(_, op)| op);

                                if let Some(op) = window {
                                    Rc::make_mut(&mut ctx).effect(Effect::Write(a));
                                    self.blocks[block_id.0].instructions.push(Residual::ExecWindow(op.window));
                                    if c == 0 {
                                        self.blocks[block_id.0].instructions.push(Residual::ExecWindow(Rc::new(SetTop::new(a + 1, &[]))));
                                    }
                                    result = Some(op.result);
                                    pure = true;
                                } else {
                                    self.blocks[block_id.0].instructions.push(Residual::NativeCall {
                                        nf: nf.native(), a: a as u16, b: b as u16, c: c as u16
                                    });
                                    // A native may allocate (a table, a string).
                                    self.blocks[block_id.0].allocates = true;
                                    pure = nf.is_pure();
                                    // See Note [Call effects].
                                    if !pure {
                                        self.join_effects(owner, Effects::OPAQUE);
                                    }
                                }
                            }
                            // Any other call may run a closure, which reads and writes the
                            // slots it captured. See Note [Captured slots].
                            let captured = if !pure {
                                captured_slots(unsafe { &*self.proto })
                            } else {
                                vec![]
                            };
                            // For a Lua callee's continuation, which applies only what the
                            // callee's effects falsify: the context before the call, but for
                            // the callee's frame, from `a` on. See Note [Call effects].
                            let before = (!native).then(|| before_call(owner, &ctx, &captured, a));
                            if !pure {
                                // An unknown call may invalidate any fragile information.
                                // See Note [Fragile information].
                                Rc::make_mut(&mut ctx).effect(Effect::Opaque);
                                // The callee may write any table, including the
                                // environment, so every witness must recheck its epoch.
                                Rc::make_mut(&mut ctx).set_hazards(None, None);
                            }
                            // The results, and the callee's frame above them, overwrote
                            // every register from `a` on: their types are unknown.
                            // TODO: compile a type specialized thunk instead? is that better?
                            let clobbered: Vec<(usize, CType)> = (a..ctx.types.len())
                                .chain(captured.into_iter().filter(|&slot| slot < a))
                                .map(|idx| (idx, CType::Unknown))
                                .collect();
                            // And the facts about them. See Note [Fragile information].
                            for &(idx, _) in &clobbered {
                                Rc::make_mut(&mut ctx).effect(Effect::Write(idx));
                            }
                            Rc::make_mut(&mut ctx).set_types(owner, clobbered);
                            if let Some(result) = &result {
                                // We know the type of the result, so can use it in our static
                                // context.
                                Rc::make_mut(&mut ctx).types[a] = result.clone();
                            }
                            Rc::make_mut(&mut ctx).top = (result.is_some() && c == 0).then_some(a + 1);
                            // The call's results arriving steps the `SubPc`, whichever
                            // function it calls. See Note [Subblocks].
                            if native {
                                if resumes {
                                    pc = pc.next_true();
                                    break 'machine;
                                }
                                return Some((pc.0 + 1, ctx, ResumeArg::Start, coro.take_held()));
                            }
                            // In a version of the call's point, for the context at the call. See
                            // Note [Call sites].
                            // Its own while the peephole holds something, which the context doesn't
                            // say. See Note [Peephole fusion] in `peephole`.
                            let holds = coro.holds_any();
                            let found = self.versions.get(&self.proto).unwrap().get(&(pc, calling.clone())).copied().filter(|_| !holds);
                            let call_block = match found {
                                Some(call_block) if call_block != block_id => {
                                    self.end_block(block_id);
                                    self.blocks[block_id.0].instructions.push(Residual::Jump(call_block));
                                    return None;
                                },
                                Some(call_block) => call_block,
                                None => {
                                    let call_block = self.new_block(pc.0);
                                    if !holds {
                                        self.blocks[call_block.0].context = Some(calling.clone());
                                        self.versions.get_mut(&self.proto).unwrap().insert((pc, calling.clone()), call_block);
                                    }
                                    #[cfg(feature = "tracing")]
                                    {
                                        let context = calling.tostring(owner);
                                        crate::tracing::instant("spec", "block", &[
                                            ("block", call_block.0.into()),
                                            ("line", self.traced_line(owner).into()),
                                            ("pc", pc.0.into()),
                                            ("context", context.as_str().into()),
                                        ]);
                                    }
                                    self.end_block(block_id);
                                    self.blocks[block_id.0].instructions.push(Residual::Jump(call_block));
                                    call_block
                                },
                            };
                            // Any other call ends its block in a thunk laying out the call
                            // for the function it finds, the code after it a version of
                            // its own. See Note [Call sites].
                            let (after, continuation) = if resumes {
                                // The generator, suspended at the call, for its returns. See Note
                                // [Call continuations].
                                let at = pc.next_true();
                                let suspended = coro.clone();
                                let rest = Rest::Resume(at, Rc::new(move |vm: &mut Specializer, owner: &mut Owner, ctx: Rc<Context>| {
                                    vm.subblock(owner, at, ctx, suspended.clone(), ResumeArg::Start)
                                }));
                                let continuation = before.filter(|_| INLINE_RESUMES).map(|(before, captured)| (before, captured, rest));
                                (After::Block(self.subblock(owner, at, ctx, coro.clone(), ResumeArg::Start)), continuation)
                            } else {
                                // A Lua callee's return also chooses a version of its own. See
                                // Note [Call continuations].
                                let continuation = before.map(|(before, captured)| (before, captured, Rest::Next(pc.0 + 1)));
                                let after = self.jumping(owner, ctx, pc.0 + 1);
                                (After::Version(pc.0 + 1, after), continuation)
                            };
                            self.end_block(call_block);
                            let thunk = self.make_call_thunk(call_block, calling, coro.clone(), self.instruction.clone(), pc, a, b, c, after, continuation, 0, true);
                            self.blocks[call_block.0].instructions.push(Residual::Thunk(thunk));
                            return None;
                        },
                    }
                },
                CoroutineState::Yielded(YieldOp::SetTypes(mut ty_effects)) => {
                    Rc::make_mut(&mut ctx).set_types(owner, ty_effects.drain(..).map(|(idx, ty)| (idx, CType::Type(ty))).collect())
                },
                CoroutineState::Yielded(YieldOp::GlobalCache(k)) => {
                    let proto = self.proto;
                    let key = LCanon::constant(unsafe { &(&(*proto).constants.items)[k] });
                    // A constant lives as long as its prototype, which the specializer's
                    // blocks do too.
                    let key: LCanon<'static, 'static> = unsafe { core::mem::transmute(key) };
                    let cache = Box::new(GlobalCache::new(key));
                    arg = ResumeArg::Cache(&*cache as *const GlobalCache);
                    self.global_caches.push(cache);
                },
                CoroutineState::Yielded(YieldOp::LoadGlobal(slot, k)) => {
                    let proto = self.proto;
                    if let crate::chunk::Constant::String(name) = unsafe { &(&(*proto).constants.items)[k] } {
                        Rc::make_mut(&mut ctx).loaded(slot, Root::Global(name_hash(name.as_bytes())), &[]);
                    }
                },
                CoroutineState::Yielded(YieldOp::SetKeyHazards(k)) => {
                    let proto = self.proto;
                    let key: &LConstant<'static, 'static> = unsafe { core::mem::transmute(&(&(*proto).constants.items)[k]) };
                    Rc::make_mut(&mut ctx).set_key_hazards(key);
                    // The global, and any field of its name, may hold another value now. See Note
                    // [Field facts].
                    if let crate::chunk::Constant::String(name) = key {
                        Rc::make_mut(&mut ctx).forget_named(Some(name_hash(name.as_bytes())));
                    }
                    // A store into the environment's hash part. See Note [Call effects].
                    self.join_effects(owner, Effects::HASH);
                },
                CoroutineState::Yielded(YieldOp::SetHazards(idx, href)) => {
                    Rc::make_mut(&mut ctx).set_hazards(idx, href);
                    // A store into a table's hash part. See Note [Call effects].
                    self.join_effects(owner, Effects::HASH);
                },
                CoroutineState::Yielded(YieldOp::Clobber(from)) => {
                    let clobbered = (from..ctx.types.len()).map(|idx| (idx, CType::Unknown)).collect();
                    Rc::make_mut(&mut ctx).set_types(owner, clobbered);
                },
                CoroutineState::Yielded(YieldOp::WidenConstant(slot)) => {
                    if ctx.types.get(slot) == Some(&CType::Type(LType::Integer)) {
                        self.widen_constant(owner, &mut ctx, slot, block_id);
                    }
                },
                CoroutineState::Yielded(YieldOp::EncodeK(..)) if let Some(how) = self.decision(owner, pc) => {
                    arg = how;
                },
                CoroutineState::Yielded(YieldOp::EncodeK(_, k)) => {
                    let proto = self.proto;
                    if let crate::chunk::Constant::Number(n) = unsafe { &(&(*proto).constants.items)[k] } && is_integer(n.0) {
                        loading = Some(self.origin(block_id, coro.clone(), pc, ctx.clone()));
                    }
                },
                CoroutineState::Yielded(YieldOp::HoldsK(slot, k)) => {
                    let proto = self.proto;
                    if let crate::chunk::Constant::Number(n) = unsafe { &(&(*proto).constants.items)[k] } && is_integer(n.0) {
                        let origin = loading.take().expect("a constant's load yields EncodeK first");
                        Rc::make_mut(&mut ctx).values.learn(Loc::root(Root::Slot(slot as u16)), Known::Constant { value: n.0 as i32, origins: Some(Rc::new(TLCell::new(vec![origin]))) });
                    }
                },
                // Found out once run, when the code it is in is laid out. See `jit.versions` in
                // `library`.
                CoroutineState::Yielded(YieldOp::Versions) => {
                    let thunk = Residual::Thunk(self.make_versions_thunk(block_id, coro.clone(), pc, ctx.clone()));
                    self.end_block(block_id);
                    self.blocks[block_id.0].instructions.push(thunk);
                    return None;
                },
                CoroutineState::Yielded(YieldOp::Narrow(slot)) => match ctx.types[slot].clone() {
                    CType::Type(LType::Integer) => {
                        // A whole constant used as an integer: kept one, and its fact had its
                        // use. See Note [Widening].
                        if let Some(value) = ctx.constant(slot) {
                            ctx.rely(owner, slot);
                            Rc::make_mut(&mut ctx).used(slot);
                        }
                        pc = pc.next_true();
                        arg = ResumeArg::Matched;
                    }
                    // Found out once forced. See Note [Narrowing].
                    CType::Type(LType::Double) => {
                        let thunk = Residual::Thunk(self.make_narrow_thunk(block_id, coro.clone(), slot, pc, ctx.clone()));
                        self.end_block(block_id);
                        self.blocks[block_id.0].instructions.push(thunk);
                        return None;
                    }
                    _ => {
                        pc = pc.next_false();
                        arg = ResumeArg::Failed;
                    }
                },
                CoroutineState::Yielded(YieldOp::SetCTypes(ty_effects)) => {
                    Rc::make_mut(&mut ctx).set_types(owner, ty_effects)
                },
                CoroutineState::Yielded(YieldOp::GetBlock(dest_pc)) => {
                    // TODO: compiling the target here recurses, and potentially blows the
                    // stack; this should probably push a thunk which compiles the block
                    // instead of a jump
                    let jumping = self.jumping(owner, ctx.clone(), dest_pc);
                    arg = ResumeArg::BlockId(self.version(owner, dest_pc, jumping));
                },
                CoroutineState::Yielded(YieldOp::GetBlockKeeping(dest_pc, kept)) => {
                    // The register the jump's own instruction wrote, which the other way to the
                    // target holds the same type in. See Note [Jumped-to contexts].
                    let jumping = self.jumping_keeping(owner, ctx.clone(), dest_pc, Some(kept));
                    arg = ResumeArg::BlockId(self.version(owner, dest_pc, jumping));
                },
                CoroutineState::Yielded(YieldOp::Jump(dest_block)) => {
                    let dest_block = self.edge(owner, &ctx, dest_block);
                    self.end_block(block_id);
                    self.blocks[block_id.0].instructions.push(Residual::Jump(dest_block));
                    // If it was a jump, stop pumping the coroutine
                    return None;
                },
                // The next instruction, streamed into the peephole holding what it holds, if it is one
                // compiled as a coroutine. See Note [Peephole fusion] in `peephole`.
                // A jump's target, the only way on, streamed into the peephole holding what it holds,
                // unless it is one the stream went on through, in the same context, or too many: a
                // loop is a block's. See Note [Peephole fusion] in `peephole`.
                CoroutineState::Yielded(YieldOp::Continue(target)) => {
                    let inst = unsafe { self.proto.as_ref().unwrap().instructions.items[target].clone() };
                    let proto = self.proto as usize;
                    let repeats = self.continued.len() >= MAX_CONTINUED
                        || self.continued.iter().any(|(of, at, known)| *of == proto && *at == target && **known == *ctx);
                    arg = match self.decode(target, &inst).filter(|_| !repeats) {
                        Some(generator) => {
                            // What a jump there carries, the stores held named by slots it keeps. See Note
                            // [Jumped-to contexts].
                            let live = unsafe { self.proto.as_ref().unwrap() }.locals_in_scope(target).unwrap_or(usize::MAX);
                            rehome(&mut coro.held, &ctx, |slot| slot >= live);
                            ctx = self.jumping(owner, ctx, target);
                            // Only a call uses the top the instruction before left. See Note [Known top].
                            if ctx.top.is_some() && !matches!(inst.0.Opcode(), Opcode::CALL | Opcode::TAILCALL) {
                                Rc::make_mut(&mut ctx).top = None;
                            }
                            let holds = self.unheld.take() != Some(target);
                            self.instruction = Some((target, Restart::Start(ctx.clone()), holds));
                            self.continued.push((proto, target, ctx.clone()));
                            coro.next_instruction(generator);
                            pc = SubPc::new(target);
                            ResumeArg::Matched
                        },
                        None => ResumeArg::Failed,
                    };
                },
                CoroutineState::Yielded(YieldOp::NextPc) => {
                    let next = pc.0 + 1;
                    let inst = unsafe { self.proto.as_ref().unwrap().instructions.items[next].clone() };
                    arg = match self.decode(next, &inst) {
                        Some(generator) => {
                            // Only a call uses the top the instruction before left. See Note [Known top].
                            if ctx.top.is_some() && !matches!(inst.0.Opcode(), Opcode::CALL | Opcode::TAILCALL) {
                                Rc::make_mut(&mut ctx).top = None;
                            }
                            let holds = self.unheld.take() != Some(next);
                            self.instruction = Some((next, Restart::Start(ctx.clone()), holds));
                            coro.next_instruction(generator);
                            pc = SubPc::new(next);
                            ResumeArg::Matched
                        },
                        None => ResumeArg::Failed,
                    };
                },
                CoroutineState::Complete(r) => {
                    return Some((pc.0 + 1, ctx, r, coro.take_held()));
                }
            } break 'machine; }
        }
    }

    pub fn run(&mut self, gc: GcCtx<'_>, owner: &mut Owner, mut id: BlockId, mut state: RunState<'src, 'intern>) -> (RunState<'src, 'intern>, FVec<LBoxed<'src, 'intern>>) {
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
            // See Note [Errors].
            if state.error.is_some() {
                (id, off) = (self.unwind(owner, &mut state), 0);
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
                        // As many inlined calls deep as the running frame's code is: the entries
                        // the interpreter has for them, the callstack's last. See Note [Inlined
                        // calls].
                        let depth = state.callstack.iter().rev().take_while(|entry| entry.returns_to().is_none()).count();
                        let offset = state.callstack.len().checked_sub(depth).filter(|_| depth > 0).map_or(state.shifted, |outer| state.base - state.callstack[outer].frame);
                        self.jit_compile(id, owner, depth, offset);
                    }

                    let mut jit_entry = self.blocks[id.0].jit_info.entry.unwrap();
                    let base_ptr = unsafe { state.vals.stack_ptr.as_non_null_ptr().add(state.base).as_ptr() };
                    warn!("running jit for {id:?} with base_ptr {base_ptr:p}");
                    state.trap = false;
                    let ret = jit_entry(&mut state, base_ptr);
                    state.finish_unwinding();
                    #[cfg(feature = "magic")]
                    if !state.force_jit.is_empty() {
                        self.force_jit(&mut state);
                    }
                    let next_off = (ret >> 32) as i32 as isize;
                    let next_id = (ret & 0xFFFFFFFF) as usize;

                    #[cfg(feature = "tracing")]
                    self.trace_bailout(owner, &state, next_off, next_id);
                    if next_off >= 0 {
                        debug!("jit exit to {next_id} {next_off}");
                        id = BlockId(next_id as usize);
                        off = next_off as usize;
                        continue;
                    } else if next_off == -1 {
                        debug!("jit bail 1 from {next_id}");
                        state.trap = false;
                        self.trip_pending(owner, &mut state);
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
                    } else if next_off == -5 {
                        // A return: the caller continues where `resume` says, and its
                        // continuation guards on `returned`. See Note [Call continuations].
                        debug!("jit return from {next_id}");
                        let Location(block, at) = Location::unpack(crate::vm::PackedLocation::from_bits(state.resume as usize));
                        id = block;
                        off = at;
                        continue;
                    } else if next_off == -4 {
                        debug!("jit bail 4 from {next_id}");
                        state.trap = false;
                        id = BlockId(next_id as usize);
                        off = state.current_off as usize;
                        // Fallthrough to immediately handle the instruction: if we have a
                        // thunk at offset=0, we don't want to jump back to the JIT again.
                    }
                }
            }
            // An error JIT code exited for. See Note [Errors].
            if state.error.is_some() {
                (id, off) = (self.unwind(owner, &mut state), 0);
                continue;
            }
            if state.gas > 0 && state.gas < 100 {
                let res = &self.blocks[id.0].instructions[off];
                println!("low gas {} at {id:?} {off} {res:?}", state.gas);
            }
            if state.gas == 0 {
                let res = &self.blocks[id.0].instructions[off];
                println!("out of gas at {id:?} {off} {res:?}");
                println!("out of gas run state: base={:?}", state.base);
                println!("out of gas return stack: {:?}", state.callstack);
                state.gas -= 1;
            }
            // See `Block::proto`.
            self.proto = self.blocks[id.0].proto as LProto<'src, 'intern>;
            // Borrowed, not cloned: an arm that needs `self` mutably (a thunk forcing, a call
            // finding its callee's version) first copies out what it uses, so no residual is
            // replaced while borrowed.
            let res = &self.blocks[id.0].instructions[off];
            state.counters.versioned_count.increment();
            debug!("RUN {:?}", res);
            match res {
                &Residual::Guard { idx, expected } | &Residual::NumericGuard { idx, expected } => {
                    if state.vals[state.base + idx].unbox().typeof_() == expected {
                        // Fallthrough
                        off += 2;
                    } else {
                        off += 1;
                    }
                },
                &Residual::NativeGuard { idx, ptr } => {
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
                &Residual::LuaGuard { idx, ptr } => {
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
                &Residual::GuardWitness { href, expected } => {
                    let witness = state.hash_witnesses[state.witness_base + href.0 as usize];
                    let value = unsafe { *witness.value.cast::<LBoxed<'_, '_>>() };
                    off += if value.unbox().typeof_() == expected { 2 } else { 1 };
                },
                &Residual::EpochCheck { tab, href, place } => {
                    if state.witness_holds(owner, tab, place, href.0) {
                        // Fallthrough
                        off += 2;
                    } else {
                        off += 1;
                    }
                },
                &Residual::HashGuard { tab, href, key, expected } => {
                    if state.witness_entry_holds(owner, tab, href.0, key, expected) {
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
                &Residual::Branch { hot, cold } => {
                    id = if state.select == 0 { hot } else { cold };
                    off = 0;
                },
                Residual::Exec(f) => {
                    off += 1;
                    (f.body)(owner, &mut state);
                    #[cfg(feature = "magic")]
                    if !state.force_jit.is_empty() {
                        self.force_jit(&mut state);
                    }
                },
                Residual::ExecWindow(w) => {
                    off += 1;
                    w.interp(owner, &mut state);
                },
                Residual::GuardDynamic(w) => {
                    w.interp(owner, &mut state);
                    off += if state.select == 1 { 2 } else { 1 };
                },
                &Residual::LuaCall { ref entry, a, b, c, stack, vararg, callee: called } => {
                    let entry = entry.clone();
                    let (caller, call) = (id, off);
                    off += 1;
                    state.call_lua(owner, Location(id, off).pack(), a, b);
                    // The closure called, which may be another of the prototype the
                    // guard checked.
                    let callee = state.clos.clone();
                    self.set_current(callee.ro(owner).prototype);
                    let block = match entry {
                        CallEntry::Block(block) => block,
                        // Found now, once. See Note [Call sites].
                        CallEntry::Context(ctx) => {
                            self.versions.entry(callee.ro(owner).prototype).or_insert_with(|| HashMap::default());
                            let block = self.version(owner, 0, ctx);
                            self.set_current(callee.ro(owner).prototype);
                            self.blocks[caller.0].instructions[call] = Residual::LuaCall { entry: CallEntry::Block(block), a, b, c, stack, vararg, callee: called };
                            block
                        },
                    };
                    id = block;
                    off = 0;
                    continue;
                },
                &Residual::TailCall { ref entry, a, b, closes, vararg, effects, callee_effects } => {
                    let entry = entry.clone();
                    let (caller, call) = (id, off);
                    // What the tail caller did, the callee's return must tell. See Note
                    // [Tail calls].
                    unsafe { (*callee_effects).set((*callee_effects).get().join((*effects).get())) };
                    state.tail_call(owner, a as usize, b as usize, closes, vararg);
                    let callee = state.clos.clone();
                    self.set_current(callee.ro(owner).prototype);
                    let block = match entry {
                        CallEntry::Block(block) => block,
                        // Found now, once. See Note [Call sites].
                        CallEntry::Context(ctx) => {
                            self.versions.entry(callee.ro(owner).prototype).or_insert_with(|| HashMap::default());
                            let block = self.version(owner, 0, ctx);
                            self.set_current(callee.ro(owner).prototype);
                            self.blocks[caller.0].instructions[call] = Residual::TailCall { entry: CallEntry::Block(block), a, b, closes, vararg, effects, callee_effects };
                            block
                        },
                    };
                    id = block;
                    off = 0;
                    continue;
                },
                &Residual::NativeCall { nf, a, b, c } => {
                    off += 1;
                    gc.publish(&state, &*self);
                    state.call_native(nf, a, b, c, owner);
                    self.trip_pending(owner, &mut state);
                },
                &Residual::Call { a, b, c } => {
                    off += 1;
                    let to_call = state.vals[state.base + a as usize].unbox();
                    debug!("{:?}", to_call);
                    // push where to return to once we RETURN
                    if let LValue::LClosure(ref lclos) = to_call {
                        let next_stack = state.call_lua(owner, Location(id, off).pack(), a, b);
                        // Either use existing block, compile a new one, or use most
                        // generic.
                        let ctx = Rc::new(Context::new(next_stack));
                        self.versions.entry(lclos.ro(owner).prototype).or_insert_with(|| HashMap::default());
                        self.set_current(lclos.ro(owner).prototype);
                        let block = self.version(owner, 0, ctx);
                        debug!("{:?} {block:?}", self.blocks);
                        self.set_current(lclos.ro(owner).prototype);
                        id = block;
                        off = 0;
                        continue;
                    } else if let LValue::NClosure(ncall) = to_call {
                        let nf = ncall.native();
                        gc.publish(&state, &*self);
                        state.call_native(nf, a as u16, b, c, owner);
                        // Past the `Arrive`: the native put its results in place.
                        // See Note [Returns].
                        off += 1;
                        self.trip_pending(owner, &mut state);
                        // FIXME(metatables): __call
                    } else {
                        // See Note [Errors].
                        let name = String::from_utf8_lossy(crate::library::type_name(state.vals[state.base + a as usize]));
                        state.raise(LBoxed::box_lvalue(LValue::OwnedString(crate::gc::Gc::string(format!("attempt to call a {name} value").as_bytes()))));
                    }
                },
                &Residual::Jump(target) | &Residual::PatchableJump(target) => {
                    id = target;
                    off = 0;
                },
                &Residual::Inline { a, b, stack, continuation, .. } => {
                    off += 1;
                    let callee = state.vals[state.base + a as usize];
                    state.shift_frame::<true>(owner, callee, a as usize, b as usize, stack, true, continuation as u64);
                    self.set_current(state.clos.ro(owner).prototype);
                },
                &Residual::Enter(by) => {
                    off += 1;
                    state.base += by as usize;
                    state.shifted += by as usize;
                },
                &Residual::Leave(by) => {
                    off += 1;
                    state.base -= by as usize;
                    state.shifted -= by as usize;
                },
                &Residual::InlineReturn { a, b, closes, moves, .. } => {
                    off += 1;
                    state.unshift_frame::<true>(owner, moves.then_some((a as usize, b as usize)), closes);
                    self.set_current(state.clos.ro(owner).prototype);
                },
                &Residual::Tripped(of) => {
                    let table = match of {
                        Some(slot) => state.vals[state.base + slot],
                        None => LBoxed::box_lvalue(LValue::Table(state._G.clone())),
                    };
                    let LValue::Table(tab) = table.unbox() else { unreachable!("a store into a table") };
                    self.trip(owner, &mut state, tab);
                    off += 1;
                },
                Residual::Thunk(thunk) => {
                    debug!("thunk {:?}", thunk);
                    // Forcing it replaces it: it runs from its own reference.
                    let thunk = thunk.clone();
                    (thunk.0.borrow_mut())(self, owner, &mut state, off);
                    self.contract(owner, &state, Location(id, off));
                },
                &Residual::Arrive { a, c } | &Residual::Arrived { a, c, .. } => {
                    off += 1;
                    state.arrive(a as usize, c as usize);
                },
                &Residual::ReturnedFrom(from) => {
                    off += if state.returned == from { 2 } else { 1 };
                },
                &Residual::Ret(_, a, b, closes, vararg, returns, effects) => {
                    debug!("spec final blocks: {:?}", self.blocks);
                    state.returned_at = Location(id, off).pack().bits() as u64;
                    match state.leave::<true>(owner, a as usize, b as usize, closes, vararg) {
                        // The interpreter runs no frame JIT code called: each has its entry.
                        Ok(None) => unreachable!("a return from a frame with no entry in the interpreter"),
                        Ok(Some(Location(block, disp))) => {
                            // See Note [Call continuations].
                            let effects = unsafe { (*effects).get() }.0 as u64;
                            state.returned = crate::vm::RETURNED | effects << crate::vm::EFFECTS_SHIFT | returns as u64;
                            self.set_current(state.clos.ro(owner).prototype);
                            id = block;
                            off = disp;
                        },
                        // The entry closure returned: its results leave the stack.
                        // See `Vm::run`.
                        Err(results) => {
                            let results = Vec::from(&state.vals[results]).into();
                            state.vals.truncate(0);
                            return (state, results);
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

    /// Unwind the pending error to the innermost protected call: pop the call's
    /// frames, if its function is a Lua function, closing their upvalues; its
    /// results are false and the error, and the code after it continues, where
    /// this returns. An error with no protected call ends the program. See Note
    /// [Errors].
    fn unwind(&mut self, owner: &mut Owner, state: &mut RunState<'src, 'intern>) -> BlockId {
        let error = state.error.take().expect("a pending error");
        state.trap = false;
        let Some(handler) = state.handlers.pop() else {
            let message = error.unbox().as_string(owner).map(|s| String::from_utf8_lossy(s.as_slice()).into_owned());
            panic!("error: {}", message.unwrap_or_else(|| format!("{:?}", error.unbox())));
        };
        if state.callstack.len() > handler.depth {
            // The call's function's frame, and every frame it called, inlined or not, are past
            // the function's slot. See Note [Inlined calls].
            state.close_upvalues_from(owner, handler.slot + 1);
            let entry = &state.callstack[handler.depth];
            let (clos, frame, witness_frame, witness_top) = (entry.clos.clone(), entry.frame, entry.witness_frame, entry.witness_top);
            state.callstack.truncate(handler.depth);
            state.clos = clos;
            state.base = frame;
            state.witness_base = witness_frame;
            state.witness_top = witness_top;
        }
        // A protected call is made from a frame made. See Note [Peephole fusion] in `peephole`.
        state.shifted = 0;
        // `c - 1` results, or both with C = 0, the top just past them.
        let results = [LBoxed::from_bool(false), error];
        let wanted = if handler.c == 0 { 2 } else { handler.c as usize - 1 };
        if handler.slot + wanted > state.vals.len() {
            state.vals.lengthen(handler.slot + wanted);
        }
        for i in 0..wanted {
            state.vals[handler.slot + i] = results.get(i).copied().unwrap_or(LBoxed::NIL);
        }
        if handler.c == 0 {
            state.top = handler.slot + 2;
        }
        self.set_current(state.clos.ro(owner).prototype);
        handler.after
    }

    /// Force the entry blocks of the prototypes `closure.__jit = ...` named (feature
    /// `magic`): each version of one compiles when next entered, with the blocks
    /// reachable from it, which keep their hotness, for building traces. Without
    /// the JIT there is nothing to compile.
    #[cfg(feature = "magic")]
    fn force_jit(&mut self, state: &mut RunState<'src, 'intern>) {
        for proto in state.force_jit.drain(..) {
            #[cfg(feature = "jit")]
            if let Some(versions) = self.versions.get(&proto) {
                for ((pc, _), block) in versions.iter() {
                    if *pc == SubPc::new(0) {
                        warn!("Forcing JIT for block {}", block.0);
                        self.blocks[block.0].jit_info.hotness.set(0);
                    }
                }
            }
            #[cfg(not(feature = "jit"))]
            let _ = proto;
        }
    }

    // TODO: this is gross! if we spec a block we have to switch current, but then forcing a thunk
    // from another function may at runtime use the wrong current closure. figure out some better
    // way (worse case each block has its own closure and we switch in run when we enter...)
    /// A `jit`/`bailout` trace event for JIT code exiting to the interpreter
    /// with `off` and `block`: why (the exit's kind, or the residual it exits
    /// at), and the function and block.
    #[cfg(feature = "tracing")]
    fn trace_bailout(&self, owner: &Owner, state: &RunState<'src, 'intern>, off: isize, block: usize) {
        // A return continues its caller where `resume` says, the block it is in, and the
        // residual at which, `off`.
        let (block, at) = match off {
            -5 => {
                let Location(BlockId(block), at) = Location::unpack(crate::vm::PackedLocation::from_bits(state.resume as usize));
                (block, at)
            }
            _ => (block, state.current_off as usize),
        };
        let reason = match off {
            -1 => "trap".to_string(),
            -2 => "return from the entry frame".to_string(),
            -3 => "select".to_string(),
            -4 => "thunk".to_string(),
            -5 => "return".to_string(),
            // A residual the JIT code doesn't run there, as a call to a function
            // with no code.
            off => format!("{}", self.blocks[block].instructions[off as usize]),
        };
        let (source, line) = Vm::info(state.clos.ro(owner).prototype);
        crate::tracing::instant("jit", "bailout", &[
            ("reason", reason.as_str().into()),
            ("block_id", block.into()),
            ("off", at.into()),
            ("source", source.as_str().into()),
            ("line", (line as u64).into()),
        ]);
    }

    pub fn set_current(&mut self, proto: LProto<'src, 'intern>) {
        self.proto = proto;
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

        fn safe_str(s: impl Into<String>) -> String {
            let s = s.into().replace("<", "\\<");
            s.replace(">", "\\>")
        }
        // A side exit never taken: a block that is only a thunk never forced.
        let untaken = |block: BlockId| matches!(self.blocks[block.0].instructions.as_slice(), [Residual::Thunk(_)]);
        // Each block's edges, labelled, and the block its code goes straight on into: a jump's,
        // or a branch's hot block where its cold one was never taken.
        let mut edges: Vec<Vec<(usize, Option<&'static str>)>> = Vec::new();
        let mut natives: Vec<Vec<String>> = Vec::new();
        let mut straight: Vec<Option<usize>> = Vec::new();
        for residuals in &self.blocks {
            let (mut out, mut calls) = (Vec::new(), Vec::new());
            for (off, res) in residuals.instructions.iter().enumerate() {
                match res {
                    Residual::Jump(target) | Residual::PatchableJump(target) => out.push((target.0, None)),
                    Residual::NativeCall { nf, .. } => calls.push(format!("\"{:p}\"", nf)),
                    Residual::Guard { .. } | Residual::NumericGuard { .. } | Residual::GuardDynamic(_) | Residual::HashGuard { .. } | Residual::GuardWitness { .. } | Residual::NativeGuard { .. } | Residual::LuaGuard { .. } => {
                        if let Some(Residual::Jump(target)) = residuals.instructions.get(off + 2) {
                            out.push((target.0, Some("pass")));
                        }
                        if let Some(Residual::Jump(target)) = residuals.instructions.get(off + 1) {
                            out.push((target.0, Some("fail")));
                        }
                    },
                    Residual::Select(targets) => out.extend(targets.iter().map(|(name, target)| (target.0, Some(*name)))),
                    Residual::Branch { hot, cold } => {
                        out.push((hot.0, Some("hot")));
                        if !untaken(*cold) {
                            out.push((cold.0, Some("cold")));
                        }
                    },
                    _ => {}
                }
            }
            straight.push(match residuals.instructions.last() {
                Some(Residual::Jump(target) | Residual::PatchableJump(target)) => Some(target.0),
                Some(Residual::Branch { hot, cold }) if untaken(*cold) => Some(hot.0),
                _ => None,
            });
            edges.push(out);
            natives.push(calls);
        }
        // Blocks drawn as the code before them goes on: the only block reaching them goes straight
        // into them. Untaken side exits aren't drawn at all.
        let mut sources: Vec<std::collections::BTreeSet<usize>> = vec![Default::default(); self.blocks.len()];
        for (from, out) in edges.iter().enumerate() {
            for &(to, _) in out {
                sources[to].insert(from);
            }
        }
        let hidden = |block: usize| untaken(BlockId(block)) && sources[block].is_empty();
        let absorbed: Vec<bool> = (0..self.blocks.len()).map(|block| {
            sources[block].len() == 1 && sources[block].iter().all(|&from| from != block && straight[from] == Some(block))
        }).collect();
        let header = |block: usize| {
            let context = reverse_versions.get(&block).map_or(String::new(), |(subpc, ctx)| {
                format!("PC: {:?}\\n{}", subpc, ctx.tostring(owner)).replace("{", "(").replace("}", ")")
            });
            #[cfg(feature = "graph")]
            let entered = format!(" x{}", self.blocks[block].entered);
            #[cfg(not(feature = "graph"))]
            let entered = "";
            (format!("{block}{entered}"), context)
        };
        let mut drawn = vec![false; self.blocks.len()];
        let mut stmts = Vec::new();
        // Heads first, then any cycle of blocks each the only way into the next.
        let order: Vec<usize> = (0..self.blocks.len()).filter(|&b| !absorbed[b]).chain((0..self.blocks.len()).filter(|&b| absorbed[b])).collect();
        for head in order {
            if drawn[head] || hidden(head) {
                continue;
            }
            let mut chain = vec![head];
            drawn[head] = true;
            while let Some(next) = straight[*chain.last().unwrap()].filter(|&next| absorbed[next] && !drawn[next]) {
                drawn[next] = true;
                chain.push(next);
            }
            let (name, context) = header(head);
            let mut rows: Vec<String> = Vec::new();
            if !context.is_empty() {
                rows.push(context);
            }
            for (i, &block) in chain.iter().enumerate() {
                if i > 0 {
                    let (name, context) = header(block);
                    rows.push(format!("→ {name}"));
                    if !context.is_empty() {
                        rows.push(context);
                    }
                }
                let instructions = &self.blocks[block].instructions;
                // The jump into the next block of the chain is the chain going on.
                let shown = if i + 1 < chain.len() && matches!(instructions.last(), Some(Residual::Jump(_) | Residual::PatchableJump(_))) { instructions.len() - 1 } else { instructions.len() };
                rows.extend(instructions[..shown].iter().map(|res| res.to_string()));
            }
            let label = safe_str(format!("\"{} | {{ {} }}\"", name, rows.join("| ")));
            stmts.push(Stmt::Node(node!(head; attr!("id", head), attr!("shape", "record"), attr!("label", label))));
            for (i, &block) in chain.iter().enumerate() {
                for &(to, label) in &edges[block] {
                    // Into the chain's next block, or into an untaken side exit: not an edge.
                    if (i + 1 < chain.len() && to == chain[i + 1] && straight[block] == Some(to)) || hidden(to) {
                        continue;
                    }
                    stmts.push(Stmt::Edge(match label {
                        Some(label) => edge!(node_id!(head) => node_id!(to); attr!("label", label)),
                        None => edge!(node_id!(head) => node_id!(to)),
                    }));
                }
                for native in &natives[block] {
                    stmts.push(Stmt::Edge(edge!(node_id!(head) => node_id!(native); attr!("label", "ncall"))));
                }
            }
        }
        let g = graph!(strict di id!("t"); subgraph!("s", stmts));

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
