#![allow(unused_variables, unused_assignments, unused)]

use std::borrow::Cow;
use std::collections::HashMap;
use std::ops::{Coroutine, CoroutineState, Deref};
use std::pin::Pin;
use std::rc::Rc;
use std::cell::{Cell, RefCell};

use crate::vm::{CallstackEntry, HashWitness, NClosure, NativeFunc, Opcode, Location, Upvalue};
use qcell::{LCell, LCellOwner};
use crate::Owner;
use crate::vm::{Tc, Vm};
use crate::vm::{BlockId, HashRef};
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
            Residual::Call { a, b, c } => write!(f, "call({}, {}, {})", a, b, c),
            Residual::Arrive { a, c } => write!(f, "arrive({}, {})", a, c),
            Residual::NativeCall { nf, a, b, c } => write!(f, "ncall({:p}, {}, {}, {})", nf, a, b, c),
            Residual::LuaCall { entry: CallEntry::Block(block), a, b, c, .. } => write!(f, "lcall({}, {}, {}, {})", block.0, a, b, c),
            Residual::LuaCall { entry: CallEntry::Context(_), a, b, c, .. } => write!(f, "lcall(?, {}, {}, {})", a, b, c),
            Residual::HashGuard { tab, href, expected, .. } => write!(f, "hguard({}, {:?}, {})", tab, href, expected),
            Residual::EpochCheck { tab, href } => write!(f, "epoch({}, {:?})", tab, href),
            Residual::Thunk(_) => write!(f, "thunk"),
            Residual::Select(targets) => write!(f, "select"),
            Residual::Ret(..) => write!(f, "ret"),
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
    TypeofK(usize), // Resumed with the type of CONSTANT[idx], for an index too wide for an rk
    IntegerK(usize), // Resumed with the value of CONSTANT[idx] as an Integer
    NumberK(usize), // Resumed with the value of CONSTANT[idx] as a Number
    BoxedK(usize), // Resumed with the value of CONSTANT[idx], as its Boxed bits
    GetBlock(Pc), // Resumed with the BlockId for calling the given PC with the current types
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
    Clobber(usize), // Inform the executor that every STACK[idx] from idx up is of unknown type
    ArrayKind(usize), // Resumed with the kind of STACK[idx]'s array part as a Type if the context
                      // knows it, else Failed. See Note [Array kinds]
    IsElementOf(usize, usize), // Resumed with Matched if STACK[a] was loaded from STACK[b]'s array
                               // part, else Failed. See Note [Array kinds]
    ArrayType(usize, usize), // Inform the executor that STACK[a] was loaded from STACK[b]'s array
                             // part: its type is the array's kind, if known. See Note [Array kinds]
    FieldType(usize, HashRef), // Inform the executor that STACK[idx]'s type is the same as an HREF's field.
                               // See Note [Field types]
    LoadUpvalue(usize, usize), // Infrom the executor that STACK[idx]'s type is the same as an UPVALUE[b].
                               // See Note [Fragile information]
    Effect(Effect), // An effect on fragile information the residuals yielded don't show. See
                    // Note [Fragile information]

    HashKey(usize, usize), // Looks up or allocates an HREF for STACK[idx][key].
    TryHashKey(usize, usize), // Look up but do not allocate an HREF.
    UpdateHashRef(HashRef, LType), // Update the type of HREF to a new type
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
    /// Its field's type. A shape or a function's identity describes a register,
    /// not a field, so a field's type is an `LType`. See Note [Field types].
    pub known_type: LType,
    /// Per slot: whether access through that slot is already checked for
    /// aliasing, so it needs no epoch check.
    pub hazards: SmallVec<[bool; 8]>,
}

impl<'src, 'intern> HashKey<'src, 'intern> {
    fn tostring(&self, owner: &Owner) -> String {
        let lv: LValue = (&self.key).into();
        format!("hkey({}, {})",
            String::from_utf8_lossy(lv.as_string_nolock().unwrap().as_slice()).to_owned().replace("\0",""),
            self.known_type)
    }

    /// A new hash key, its type not yet discovered.
    fn new(idx: usize, key: LConstant<'src, 'intern>) -> Self {
        HashKey { idx, key, known_type: LType::Unknown, hazards: Default::default() }
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

    /// Whether this index is free for a new hash key: its type is unknown and no
    /// shape lists it. A live hash key can also have an unknown type briefly
    /// (before its field's type is discovered), but then a shape lists it.
    fn orphan(&self, href: HashRef, types: &[CType]) -> bool {
        self.known_type == LType::Unknown
            && !types.iter().any(|ctype| matches!(ctype, CType::Shape(hrefs) if hrefs.contains(&href)))
    }

    /// Whether blocks compiled knowing `self` are correct for a context with
    /// `other` at the same index. See Note [Version compatibility].
    fn accepts(&self, other: &Self) -> bool {
        self.idx == other.idx
            && self.key == other.key
            && self.known_type.accepts(other.known_type)
            && self.hazards.iter().enumerate().all(|(slot, &checked)| !checked || other.hazards.get(slot) == Some(&true))
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
    HashRef(HashRef, LType),
    Integer(i32),
    Number(f64),
    Boxed(u64),
    /// See Note [Global caches].
    Cache(*const GlobalCache),
    /// The end of a call's arguments, and the type its native's window op
    /// assumes they have.
    WindowArgs(usize, CType),
}

// Initialize a hash key. `at` is `index << 8 | href`. Populate the witness `at` with `key`,
// proving it both exists and is at the correct offset `index` for `tab`. See Note [Hash witnesses].
// Selects 0 if the table has the key and 1 if not.
windowed!(HrefInit, [at: u64, key: u64], [], |owner, state, base| (table) {
    let (href, index) = (at as u8, (at >> 8) as usize);
    let hidx = state.witness_base + href as usize;
    let LValue::Table(tab) = table.unbox() else { unreachable!() };
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
            state.hash_witnesses[hidx] = HashWitness { epoch, index, value: value.cast() };
            state.select = 0;
        },
        // The slow path is intentionally out of line, for code size reasons.
        _ => href_init_slow(owner, state, table, href, index, key),
    }
});

/// `HrefInit` when the key isn't at `index`, or the witness's slot isn't there yet. Also handles
/// growing the witness vector, which is also unlikely. `rust-cold` (LLVM's `preserve_most`), so
/// the callee saves the registers it uses and the stencil's fast path needn't save its window
/// around the call.
extern "rust-cold" fn href_init_slow<'src, 'intern>(owner: &mut Owner, state: &mut RunState<'src, 'intern>, table: LBoxed<'src, 'intern>, href: u8, index: usize, key: u64) {
    let hidx = state.witness_base + href as usize;
    if state.hash_witnesses.len() <= hidx {
        state.hash_witnesses.resize_with(hidx + 1, HashWitness::default);
    }
    state.witness_top = state.witness_top.max(hidx + 1);
    // Safety: the key is a constant's, which outlives the code using it.
    let key: LCanon<'src, 'intern> = unsafe { LCanon::from_bits(key) };
    let LValue::Table(tab) = table.unbox() else { unreachable!() };
    let found = match tab.ro(owner).hash.get_index(index) {
        Some((k, _)) if *k == key => Some(index),
        _ => tab.ro(owner).hash.get_index_of(&key),
    };
    let tab = tab.rw(owner);
    let epoch = tab.epoch;
    state.hash_witnesses[hidx] = match found {
        Some(index) => {
            state.select = 0;
            let value = tab.hash.get_index_mut(index).unwrap().1 as *mut LBoxed<'_, '_>;
            HashWitness { epoch, index, value: value.cast() }
        },
        None => {
            debug!("href_init missing key");
            state.select = 1;
            HashWitness { epoch, index, value: core::ptr::null_mut() }
        },
    };
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
// forgotten after each call, and no context types a captured slot with what a call may have
// changed.
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
// A lua call must returns to its `Arrive`: its `Location` is the `Arrive`, so
// every way back into the caller takes its results there, whether the callee
// returns to the caller's JIT code, to the interpreter running the caller, or
// through a bailout.
// A native call *must not*; `call_native` puts the results in place by itself, and running
// `Arrive` additionally would be incorrect. For known native functions we may skip emitting the
// `Arrive` in the first place. However, for dynamic calls where it is not known until runtime if a
// callee is a lua or native function, it must dynamically perform a jump.

// Note [Frame ops]
// ~~~~~~~~~~~~~~~~
// JIT code and the interpreter share one Lua call stack: `state.callstack`, and the running frame
// in `state`. Whenever control leaves JIT code, the frames there must be exactly what the
// interpreter would have.
// No Lua frame exists only in the native stack, so a bailout just discards
// JIT code's native frames and resumes the suspended Lua frame in the interpreter.
//
// JIT code keeps the callstack intact by running the interpreter's own frame maintenance
// functions, not a copy of the logic. Each one is ran as a window op, copied into the JIT code,
// which means that the size of each function is very size and branch prediction sensitive.

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

    /// The value, of this count, a hole holding `held` (`hold`) stands for.
    pub fn lift(self, held: u16) -> usize {
        match self {
            Count::Zero => 0,
            Count::One => 1,
            Count::Two => 2,
            Count::Many => held as usize + 3,
        }
    }
}

// `call_lua` for a call of R(A). `abs` is its `a | b << 16 | stack << 32` (A and B as
// `Count::hold` holds them, `stack` the callee's `max_stack`). The pushed frame returns to `ret`
// (a `PackedLocation`). Requires nilling the callee's frame if `FILLS`, or else the JIT code does.
// The callee isn't vararg: its frame's entry records no function slot (Note [Vararg frames]).
// See Note [Frame ops].
windowed!(frame PushFrame, [ret: u64, abs: u64], [FILLS: bool, A: Count, B: Count], |owner, state, base| () {
    let (a, b) = (A.lift(abs as u16), B.lift((abs >> 16) as u16));
    state.push_frame(owner, crate::vm::PackedLocation::from_bits(ret as usize), a, b, (abs >> 32) as u8, FILLS);
    debug_assert!(unsafe { (*state.clos.ro(owner).prototype).is_vararg } == 0, "PushFrame of a vararg function's frame");
});

// A `Ret` at `at` (a `PackedLocation`). `ab` is its `a | b << 16` (as `Count::hold` holds them).
// Closing upvalues if `CLOSES`, returning from a vararg function if `VARARG`.
// See Note [Frame ops].
windowed!(frame PopFrame, [at: u64, ab: u64], [CLOSES: bool, VARARG: bool, A: Count, B: Count], |owner, state, base| () {
    let Location(BlockId(block), off) = Location::unpack(crate::vm::PackedLocation::from_bits(at as usize));
    let (a, b) = (A.lift(ab as u16), B.lift((ab >> 16) as u16));
    state.exit = if state.callstack.is_empty() {
        state.current_off = off as u16;
        ((-2i32 as u64) << 32) | block as u64
    } else {
        match state.leave(owner, a, b, CLOSES, VARARG) {
            Ok(location) => location.pack().bits() as u64,
            // With a caller frame, `leave` returns to it.
            Err(_) => unreachable!(),
        }
    };
});

// Whether a table's array part has kind `kind`, testing an element loaded from it in place of
// the element's own tag. See Note [Array kinds].
windowed!(KindIs, [kind: LType], [], |owner, state, base| (table) {
    let LValue::Table(tab) = table.unbox() else { unreachable!() };
    state.select = (tab.ro(owner).kind != kind.bit()) as usize;
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
    /// A guard whose test is a window op: it sets `state.select` to 0 if passed, or 1 if failed.
    /// See Note [Dynamic guards].
    GuardDynamic(Rc<dyn Window>),
    Call { a: u16, b: u16, c: u16 },
    Select(Vec<(&'static str, BlockId)>),
    Jump(BlockId),
    Thunk(ThunkRef),
    /// A RETURN of `b - 1` values from R(A), or up to the top. Closes the frame's open upvalues.
    /// Functions which statically know they have no open upvalues may set `close = false` as an
    /// optimization. Last, whether the function is vararg. See Note [Vararg frames].
    Ret(Pc, u8, u16, bool, bool),
    /// Whether the witness `href`'s index in the table in `tab` still holds its
    /// key, `key` (canonical bits), with a value of type `expected`.
    HashGuard { tab: usize, href: HashRef, key: u64, expected: LType },
    EpochCheck { tab: usize, href: HashRef },
    NativeGuard { idx: usize, ptr: *const () },
    NativeCall { nf: NativeFunc, a: u16, b: u16, c: u16 },
    /// A call to the Lua function in R(A), The target `entry` is a prototype a `LuaGuard` or the
    /// context knows. Sizes the newly pushed frame to `stack` slots (the prototype's `max_stack`).
    /// `vararg` if the prototype is vararg (Note [Vararg frames]). See Note [Call sites].
    LuaCall { entry: CallEntry, a: u16, b: u16, c: u16, stack: u8, vararg: bool },
    /// The results of the call of R(A) before it, which returns here: `c - 1`
    /// of them, or with C = 0 all. See Note [Returns].
    Arrive { a: u16, c: u16 },
    LuaGuard { idx: usize, ptr: *const () },
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

/// The context a call in `caller`, of R(A) with operand B, enters the callee
/// `proto` with. See Note [Call sites].
fn entry_context<C>(caller: &Context, proto: &crate::chunk::FunctionBlock<'_, C>, a: usize, b: usize) -> Context {
    let slots = proto.max_stack as usize;
    let mut entry = Context::new(vec![LType::Unknown; slots]);
    let passed = if b != 0 { Some(b - 1) } else { caller.top.map(|top| top.saturating_sub(a + 1)) };
    let Some(passed) = passed.filter(|_| proto.is_vararg == 0) else { return entry };
    for param in 0..(proto.param_count as usize).min(slots) {
        entry.types[param] = if param >= passed {
            CType::Type(LType::Nil)
        } else {
            match caller.slot(a + 1 + param) {
                CType::Shape(_) => CType::Type(LType::Table),
                ctype => ctype,
            }
        };
    }
    entry
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum CType {
    Type(LType),
    /// A number in either encoding, `Integer` or `Double`.
    Number,
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
    pub(crate) fn accepts(&self, other: &CType) -> bool {
        match (self, other) {
            (a, b) if a == b => true,
            (CType::Number, CType::Type(LType::Integer | LType::Double)) => true,
            // A shape or a function's identity is below its table or closure.
            (CType::Type(a), b) => a.accepts(b.as_ltype()),
            _ => false,
        }
    }

    /// The type's height in the lattice: how much it tells.
    fn depth(&self) -> usize {
        match self {
            CType::Type(LType::Unknown) => 0,
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
            CType::Type(self.as_ltype().join(other.as_ltype()))
        }
    }

    /// Convert a CType to an LType, potentially losing static information.
    pub(crate) fn as_ltype(&self) -> LType {
        match self {
            CType::Type(ty) => ty.clone(),
            CType::Number => LType::Unknown,
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
            CType::Number => write!(f, "number"),
            CType::Shape(shape) => write!(f, "shape({})", shape.iter().map(|hr| hr.0.to_string()).intersperse(",".to_string()).collect::<String>()),
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

/// Where a guard for `expected` continues its generator, with what, when the value's type is
/// `found`. Each step down the lattice translates into one SubPc step, so that continuing the
/// generator at different `found` but to the same `expected` reach the same state and so can be
/// potentially deduplicated. See Note [Subblock].
fn navigate(pc: SubPc, expected: &CType, found: &CType) -> (SubPc, ResumeArg) {
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
// a hash lookup. Nothing about globals goes in the context: which globals a path
// happens to touch would otherwise split versions at every merge.
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
// So a new href starts with an unknown type, and the load after it discovers
// the type (`FieldType`): the loaded slot gets an ordinary type guard, and the
// type it finds becomes the hash key's too. Later loads through the same hash key
// use that type without a guard.
//
// The type stays valid while the witness has the table's current epoch, because
// anything that changes a field's type bumps the epoch: a witness store per its
// `Retype` (never `Same` for an unknown type), and a generic store whose value's
// type differs. When an access finds the epoch changed, `HashGuard` checks the
// type again; if that fails it falls back to a fresh href, which rediscovers the
// type and can rejoin the blocks already compiled for it.
//
// A field's type is only ever an `LType`: a shape or a function's identity
// describes a register, not a field.

/// Whether a jump forgets a type of a register holding no local in scope at
/// its target, which may still be an expression's temporary (`a and b or c`).
fn forgotten(ctype: &CType) -> bool {
    *ctype != CType::Type(LType::Unknown)
}

/// Whether a jump to a target where the registers from `live` on hold no local
/// forgets anything of `ctx`: those registers' types (`forgotten`), and the
/// fragile facts about them.
fn forgets(ctx: &Context, live: usize) -> bool {
    (live..ctx.types.len()).any(|idx| forgotten(&ctx.types[idx]) || ctx.fragile.iter().any(|fact| !fact.survives(Effect::Write(idx))))
}

/// Forget, for a jump to a target where the registers from `live` on hold no
/// local, those registers' types and the fragile facts about them.
fn forget_dead(owner: &mut Owner, ctx: &mut Context, live: usize) {
    let dead = (live..ctx.types.len()).filter(|&idx| forgotten(&ctx.types[idx])).map(|idx| (idx, CType::Type(LType::Unknown))).collect();
    ctx.set_types(owner, dead);
    for idx in live..ctx.types.len() {
        ctx.effect(Effect::Write(idx));
    }
}

// Note [Dynamic guards]
// ~~~~~~~~~~~~~~~~~~~~~~
// A `GuardDynamic` residual's test is a window op that reads its operands and sets `state.select`,
// 0 to pass and 1 to fail, and is otherwise pure. Its two edges continue the generator at
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

/// The type of a constant.
fn constant_ctype<S: PartialEq + Eq>(k: &crate::chunk::Constant<S>) -> CType {
    match k {
        crate::chunk::Constant::Nil => CType::Type(LType::Nil),
        crate::chunk::Constant::Bool(_) => CType::Type(LType::Bool),
        crate::chunk::Constant::Number(n) if is_integer(n.0) => CType::Type(LType::Integer),
        crate::chunk::Constant::Number(_) => CType::Type(LType::Double),
        crate::chunk::Constant::String(_) => CType::Type(LType::String),
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
// (a shape accepts only itself). A version for a table in a slot is correct for
// a shape there: the jump's hash keys on it are extra keys the version doesn't
// know, as below. The join relies on this, widening shapes to tables.
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
    /// The frame's top, as a slot, when the instruction before left it at one
    /// the specializer knows. See Note [Known top].
    pub top: Option<usize>,
    /// What the specializer assumes and no guard checks, in `Fragile::key`
    /// order. See Note [Fragile information].
    pub fragile: SmallVec<[Fragile; 2]>,
}

// Note [Array kinds]
// ~~~~~~~~~~~~~~~~~~
// A table's array part has a kind: the representations of the values stored in it since it was
// last emptied, one bit each, which every store sets with no test. It is of a single kind when one
// bit is set, and mixed once two are. A kind only widens while the array holds values, so a table
// of a single kind holds only values of it.
//
// The context learns kinds as fragile information. A load from an array part of known kind has
// that type with no test. Any other load's slot is an element of its table (`ElementOf`), and a
// guard finding out its representation, if the array's kind is that representation, tests the
// array's kind in place of the element's: an element loaded before is covered, as the kind only
// widened since, and the kind is known after (`Kind`). An array that isn't of the element's
// representation has the element tested, as any value. A loop's first iteration learns the kinds
// of the arrays it reads elements of, so its later iterations, versioned for what the back edges
// carry, read them unguarded.
//
// A guard finding out the representation of an element of a mixed array knows that too
// (`Kind` of `Unknown`): it stays mixed however it is stored into, and a store into it needn't
// widen its kind, which no guard then tests.
//
// Every store into an array part widens its kind, but for a value of a kind the context knows the
// array has, or an element of the same array, which its kind covers. A store may be into any table
// the context knows the kind of, through another slot, so it keeps only the known kinds of the
// value's representation; an element stored back into its own array changes no kind.

// Note [Fragile information]
// ~~~~~~~~~~~~~~~~~~~~~~~~~~
// Fragile information is speculation the specializer assumes under a closed-world model, with no
// guard to check it: once established, a fact holds until an effect the specializer sees could
// falsify it, where it is dropped without repair. Every effect that could falsify a fact must be
// visible; where the closed world can't be shown to hold, such as across code the specializer
// doesn't see all of it is dropped. The known top (Note [Known top]) is information of this kind.
//
// It is in the context (`Context::fragile`), so it is part of every block's key. A block compiled
// relying on a fact is only entered by paths that established it and kept it since, as any path
// reaching a block with an equal context shares it. It is per activation: a function's entry block
// has none, and a call's continuation none either, after the call's effect.
//
// Effects come from the residuals as they are yielded (`Context::effect`). A window op writes the
// slots its accesses say it writes (`Effect::Write`), an exec may write any slot
// (`Effect::WriteAny`; it runs no Lua code), a call that isn't a window op is `Effect::Opaque`,
// and what a residual can't show a yield says (`YieldOp::Effect`: SETUPVAL's
// `Effect::SetUpvalue`).
//
// A kind of fact says which effects it survives (`Fragile::survives`); a new kind is a variant,
// its `key` and `survives`, and where it is established.
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
// Instead the versions of a pc that differ only in their facts are kept ordered by inclusion, each
// one's facts a subset of the next's, and a context reaching the pc forgets whatever facts it has
// that would break that order. Dropping facts is always sound, since a version relying on fewer
// facts accepts any context with more, and n facts then give at most n + 1 versions.
//
// Which facts a path keeps depends on the order paths are compiled in. Facts established before a
// loop's paths diverge reach every back edge, and are kept by all of them; a path that establishes
// more than an existing version keeps them in a version of its own; and a path whose facts are
// incomparable with one compiled before it keeps only those the two share.

/// Speculation the specializer assumes without a guard. See Note [Fragile
/// information].
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Fragile {
    /// Stack slot `slot` holds the value upvalue `upvalue` held when loaded
    /// into it.
    Holds { slot: usize, upvalue: usize },
    /// Upvalue `upvalue` holds a value of `ctype`: a native function's, which
    /// is its identity.
    Upvalue { upvalue: usize, ctype: CType },
    /// Stack slot `slot` holds a value loaded from the array part of the table
    /// in slot `table`. See Note [Array kinds].
    ElementOf { slot: usize, table: usize },
    /// The array part of the table in slot `table` has kind `kind`: `Unknown`
    /// if mixed. See Note [Array kinds].
    Kind { table: usize, kind: LType },
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
    /// Code the specializer doesn't see runs: every fact is dropped.
    Opaque,
    /// A value of representation `LType` (`Unknown` if not known) is stored in
    /// some table's array part.
    ArrayStore(LType),
}

impl Fragile {
    /// What the fact is about, unique among a context's facts, and their order.
    fn key(&self) -> (u8, usize) {
        match self {
            Fragile::Holds { slot, .. } => (0, *slot),
            Fragile::Upvalue { upvalue, .. } => (1, *upvalue),
            Fragile::ElementOf { slot, .. } => (2, *slot),
            Fragile::Kind { table, .. } => (3, *table),
        }
    }

    /// Whether the fact still holds after `effect`.
    fn survives(&self, effect: Effect) -> bool {
        match (self, effect) {
            (_, Effect::Opaque) => false,
            (Fragile::Holds { slot, .. }, Effect::Write(written)) => written != *slot,
            (Fragile::Holds { .. }, Effect::WriteAny) => false,
            (Fragile::Holds { upvalue, .. } | Fragile::Upvalue { upvalue, .. }, Effect::SetUpvalue(set)) => set != *upvalue,
            (Fragile::Upvalue { .. }, Effect::Write(_) | Effect::WriteAny) => true,
            (Fragile::Holds { .. } | Fragile::Upvalue { .. }, Effect::ArrayStore(_)) => true,
            (Fragile::ElementOf { slot, table }, Effect::Write(written)) => written != *slot && written != *table,
            (Fragile::Kind { table, .. }, Effect::Write(written)) => written != *table,
            (Fragile::ElementOf { .. } | Fragile::Kind { .. }, Effect::WriteAny) => false,
            (Fragile::ElementOf { .. } | Fragile::Kind { .. }, Effect::SetUpvalue(_)) => true,
            // The value stays where it was loaded from.
            (Fragile::ElementOf { .. }, Effect::ArrayStore(_)) => true,
            // Any table may be the one stored into: one of kind `kind` keeps it
            // only for a value of that kind, and a mixed one stays mixed.
            (Fragile::Kind { kind, .. }, Effect::ArrayStore(stored)) => *kind == LType::Unknown || stored == *kind,
        }
    }
}

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
        for fact in &self.fragile {
            if let Fragile::Upvalue { ctype, .. } = fact {
                ctype.mark(owner);
            }
        }
    }
}

impl Context {
    pub fn new(mut types: Vec<LType>) -> Self {
        Self {
            types: types.drain(..).map(|t| CType::Type(t)).collect(),
            hkeys: vec![],
            top: None,
            fragile: SmallVec::new(),
        }
    }

    fn tostring(&self, owner: &Owner) -> String {
        format!("context([{}], hkeys: {}, fragile: {:?})",
            self.types.iter().map(|t| format!("{}", t)).intersperse(",".to_string()).collect::<String>(),
            self.hkeys.iter().map(|hk| hk.tostring(owner)).intersperse(",".to_string()).collect::<String>(),
            self.fragile,
        )
    }

    /// Assume `fact`, in place of any about the same thing. See Note [Fragile
    /// information].
    fn assume(&mut self, fact: Fragile) {
        self.fragile.retain(|known| known.key() != fact.key());
        self.fragile.push(fact);
        self.fragile.sort_by_key(|fact| fact.key());
    }

    /// Drop the facts `effect` may falsify. See Note [Fragile information].
    fn effect(&mut self, effect: Effect) {
        self.fragile.retain(|fact| fact.survives(effect));
    }

    /// The kind of the array part of the table in slot `table`, if known. See
    /// Note [Array kinds].
    fn array_kind(&self, table: usize) -> Option<LType> {
        self.fragile.iter().find_map(|fact| match fact {
            Fragile::Kind { table: known, kind } if *known == table => Some(*kind),
            _ => None,
        })
    }

    /// The slot of the table whose array part slot `slot`'s value was loaded
    /// from, if known. See Note [Array kinds].
    fn element_of(&self, slot: usize) -> Option<usize> {
        self.fragile.iter().find_map(|fact| match fact {
            Fragile::ElementOf { slot: loaded, table } if *loaded == slot => Some(*table),
            _ => None,
        })
    }

    /// The upvalue whose value slot `slot` holds, if known.
    fn holds(&self, slot: usize) -> Option<usize> {
        self.fragile.iter().find_map(|fact| match fact {
            Fragile::Holds { slot: held, upvalue } if *held == slot => Some(*upvalue),
            _ => None,
        })
    }

    /// The type of upvalue `upvalue`'s value, if known.
    fn upvalue(&self, upvalue: usize) -> Option<&CType> {
        self.fragile.iter().find_map(|fact| match fact {
            Fragile::Upvalue { upvalue: known, ctype } if *known == upvalue => Some(ctype),
            _ => None,
        })
    }

    /// Whether `other` has every fact `self` has.
    fn fragile_within(&self, other: &Context) -> bool {
        self.fragile.iter().all(|fact| other.fragile.contains(fact))
    }

    /// Whether `self` and `other` differ at most in fragile information.
    fn alike(&self, other: &Context) -> bool {
        self.types == other.types && self.hkeys == other.hkeys && self.top == other.top
    }

    /// The type of slot `idx`: unknown past the end.
    fn slot(&self, idx: usize) -> CType {
        self.types.get(idx).cloned().unwrap_or(CType::Type(LType::Unknown))
    }

    /// Whether a block specialized to `self` is correct in `other`. See Note
    /// [Version compatibility].
    fn accepts(&self, other: &Context) -> bool {
        self.hkeys.iter().enumerate().all(|(i, hkey)| {
            hkey.orphan(HashRef(i as u8), &self.types) || other.hkeys.get(i).is_some_and(|theirs| hkey.accepts(theirs))
        })
            && (self.top.is_none() || self.top == other.top)
            && self.fragile_within(other)
            && (0..self.types.len().max(other.types.len())).all(|idx| self.slot(idx).accepts(&other.slot(idx)))
    }

    /// The lattice height `self` loses from `other`, which it accepts.
    fn distance(&self, other: &Context) -> usize {
        (0..self.types.len().max(other.types.len())).map(|idx| other.slot(idx).depth() - self.slot(idx).depth()).sum::<usize>()
            + (other.fragile.len() - self.fragile.len())
    }

    /// Widen `self` to also accept `other`. Differing hash keys can't be merged,
    /// so then every shape and hash key is dropped.
    fn join(&mut self, owner: &mut Owner, other: &Context) {
        let widened: Vec<(usize, CType)> = (0..self.types.len())
            .filter_map(|idx| {
                let joined = self.types[idx].join(&other.slot(idx));
                (joined != self.types[idx]).then_some((idx, joined))
            })
            .collect();
        self.set_types(owner, widened);
        if self.top != other.top {
            self.top = None;
        }
        self.fragile.retain(|fact| other.fragile.contains(fact));
        if self.hkeys != other.hkeys {
            let shapes: Vec<(usize, CType)> = (0..self.types.len())
                .filter(|&idx| matches!(self.types[idx], CType::Shape(_)))
                .map(|idx| (idx, CType::Type(LType::Table)))
                .collect();
            self.set_types(owner, shapes);
            // What's left are orphans: with none, the joined version accepts any
            // hash keys.
            self.hkeys.clear();
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
                        key.known_type = LType::Unknown;
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
    /// Make every hash key of `key` check the epoch again.
    pub fn set_key_hazards(&mut self, key: &LConstant<'static, 'static>) {
        for hkey in self.hkeys.iter_mut().filter(|hkey| hkey.key == *key) {
            hkey.clear_checks();
        }
    }

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
            self.hkeys[invalid as usize].clear_checks();
        }
    }
}

pub struct Specializer<'src, 'intern> {
    pub blocks: Vec<Block>,
    pub clos: Tc<LClosure<'src, 'intern>>,
    #[cfg(feature = "jit")]
    pub jctx: JitContext,

    /// The global caches its blocks use, at stable addresses. See Note [Global
    /// caches].
    pub global_caches: Vec<Box<GlobalCache>>,
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
            global_caches: Vec::new(),
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
        // Versions differing only in fragile information are a chain of subsets,
        // each version's facts in the next's: `ctx` keeps the most facts that
        // keep it one. See Note [Fragile information].
        let mut chain: Vec<&(Rc<Context>, BlockId)> = existing.iter().filter(|(ectx, _)| ectx.alike(&ctx)).collect();
        chain.sort_by_key(|(ectx, _)| ectx.fragile.len());
        let below = chain.iter().rposition(|(ectx, _)| ectx.fragile_within(&ctx));
        // Above the top every fact is kept; otherwise those shared with the
        // version above the highest `ctx` has all of, or with the bottom.
        let bound = match below {
            Some(below) => chain.get(below + 1),
            None => chain.first(),
        };
        let ctx = match bound {
            Some((above, _)) => {
                let mut lowered = (*ctx).clone();
                lowered.fragile.retain(|fact| above.fragile.contains(fact));
                if let Some((under, block)) = below.map(|below| chain[below]) {
                    if under.fragile == lowered.fragile {
                        return *block;
                    }
                }
                Rc::new(lowered)
            },
            None => ctx,
        };
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
            // Only a CALL uses the top the instruction before left. See Note [Known top].
            if ctx.top.is_some() && inst.0.Opcode() != Opcode::CALL {
                Rc::make_mut(&mut ctx).top = None;
            }
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
                Opcode::TESTSET => {
                    let (a, b, c) = crate::vm::ABC::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_testset(a as usize, b as usize, c, pc + 1)), ResumeArg::Start, block_id)
                },
                Opcode::NOT => {
                    let (a, b) = crate::vm::AB::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_not(a as usize, b as usize)), ResumeArg::Start, block_id)
                },
                Opcode::CLOSE => {
                    let (a, _) = crate::vm::AB::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_close(a as usize)), ResumeArg::Start, block_id)
                },
                Opcode::TFORLOOP => {
                    let (a, _, c) = crate::vm::ABC::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_tforloop(a as usize, c as usize, pc + 1)), ResumeArg::Start, block_id)
                },
                Opcode::VARARG => {
                    let (a, b) = crate::vm::AB::unpack(inst.0);
                    let params = unsafe { (*self.clos.ro(owner).prototype).param_count as usize };
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_vararg(a as usize, b as usize, params)), ResumeArg::Start, block_id)
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
                Opcode::SETUPVAL => {
                    let (a, b) = crate::vm::AB::unpack(inst.0);
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_setupval(a as usize, b as usize)), ResumeArg::Start, block_id)
                },
                Opcode::CLOSURE => {
                    let (a, bx) = crate::vm::ABx::unpack(inst.0);
                    let proto = unsafe { &*self.clos.ro(owner).prototype };
                    let count = proto.prototypes.items[bx as usize].upval_count as usize;
                    let upvalues = proto.instructions.items[pc + 1..pc + 1 + count].iter()
                        .map(|pseudo| (pseudo.0.Opcode(), crate::vm::AB::unpack(pseudo.0).1 as usize))
                        .collect();
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_closure(a as usize, bx as usize, upvalues, pc + 1 + count)), ResumeArg::Start, block_id)
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
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_getglobal(a as usize, bx as usize)), ResumeArg::Start, block_id)
                },
                Opcode::SETGLOBAL => {
                    let (a, bx) = crate::vm::ABx::unpack(inst.0);
                    let kst = unsafe { &(&(*self.clos.ro(owner).prototype).constants.items)[bx as usize] };
                    self.compile_one(owner, SubPc::new(pc), ctx.clone(), Box::new(emit_setglobal(a as usize, bx as usize)), ResumeArg::Start, block_id)
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
                    self.end_block(block_id);
                    let proto = unsafe { &*self.clos.ro(owner).prototype };
                    let closes = !captured_slots(proto).is_empty();
                    self.blocks[block_id.0].instructions.push(Residual::Ret(pc, a, b, closes, proto.is_vararg != 0)); None
                },
                x => {
                    #[cfg(debug_assertions)]
                    {
                        unreachable!("{:?}", x)
                    }
                    panic!("{:?}", x);
                    let vararg = unsafe { (*self.clos.ro(owner).prototype).is_vararg != 0 };
                    self.blocks[block_id.0].instructions.push(Residual::Ret(pc, 0, 0, true, vararg)); None
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

    /// Where a jump in `ctx` to `target` goes: `target`, a version of a pc whose
    /// context accepts the jump's, once it forgets the types of registers
    /// holding no local (`forgotten`). See Note [Version compatibility].
    fn edge(&mut self, owner: &mut Owner, ctx: &Context, target: BlockId) -> BlockId {
        let Some(entered) = self.blocks[target.0].context.clone() else { return target };
        let pc = self.blocks[target.0].pc;
        let live = unsafe { self.clos.ro(owner).prototype.as_ref().unwrap() }.locals_in_scope(pc).unwrap_or(usize::MAX);
        let mut jumping = ctx.clone();
        forget_dead(owner, &mut jumping, live);
        assert!(entered.accepts(&jumping), "a jump in {} to a version for {}", jumping.tostring(owner), entered.tostring(owner));
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
    /// version.
    fn jumping(&self, owner: &mut Owner, mut ctx: Rc<Context>, dest_pc: Pc) -> Rc<Context> {
        let in_scope = unsafe { self.clos.ro(owner).prototype.as_ref().unwrap() }.locals_in_scope(dest_pc);
        if let Some(in_scope) = in_scope.filter(|&in_scope| forgets(&ctx, in_scope)) {
            forget_dead(owner, Rc::make_mut(&mut ctx), in_scope);
        }
        // An element of a known type was guarded, or its array's kind is known:
        // what it was loaded from tells no more. Only the version jumped to is
        // found without it, so it still accepts the jump. See Note [Array kinds].
        let typed = |fact: &Fragile| matches!(fact, Fragile::ElementOf { slot, .. } if ctx.slot(*slot) != CType::Type(LType::Unknown));
        if ctx.fragile.iter().any(typed) {
            let forgotten: Vec<Fragile> = ctx.fragile.iter().filter(|fact| typed(fact)).cloned().collect();
            Rc::make_mut(&mut ctx).fragile.retain(|fact| !forgotten.contains(fact));
        }
        ctx
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

    /// The thunk a `Guard(idx, t)` (`expected` `CType::Type(t)`) or a
    /// `GuardCType(idx, expected)` ends its block in when the context can't
    /// answer it.
    /// With `field`, the slot was just loaded from that hash key's field
    /// (`FieldType`), whose type is the one found too. See Note [Field types].
    /// A thunk finding out the type of STACK[idx] for a guard of `expected`.
    /// A function found gets its identity guarded too, unless the chain of
    /// thunks this one is in guards `identities` of them already, `MAX_VERSIONS`
    /// (Note [Call sites]).
    fn make_discovery_thunk(&self, mut block_id: BlockId, thunk_coro: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>, idx: usize, expected: CType, field: Option<HashRef>, pc: SubPc, mut thunk_ctx: Rc<Context>, appends: bool, identities: usize) -> ThunkRef {

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
            let array = thunk_ctx.element_of(idx).map(|table| {
                let LValue::Table(tab) = state.vals[state.base + table].unbox() else { unreachable!("an element of a slot not holding a table") };
                (table, tab.ro(owner).kind)
            });
            let kind_of = array.filter(|&(_, kind)| kind == found_field.bit()).map(|(table, _)| table);
            // A value the context knows is a number only has its encoding tested.
            let guard = if let Some(table) = kind_of {
                Residual::GuardDynamic(Rc::new(KindIs::new(found_field, &[table])))
            } else if thunk_ctx.types[idx] == CType::Number {
                Residual::NumericGuard { idx, expected: found_field }
            } else {
                Residual::Guard { idx, expected: found_field }
            };
            let mut forced_ctx = thunk_ctx.clone();;
            let mut forced_mut = Rc::make_mut(&mut forced_ctx);
            forced_mut.types[idx] = found.clone();
            if let Some(table) = kind_of {
                forced_mut.assume(Fragile::Kind { table, kind: found_field });
            }
            // An array of two representations or more stays mixed.
            if let Some((table, _)) = array.filter(|&(_, kind)| kind.count_ones() > 1) {
                forced_mut.assume(Fragile::Kind { table, kind: LType::Unknown });
            }
            if let Some(href) = field {
                forced_mut.hkeys[href.0 as usize].known_type = found_field;
            }
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
                // A slot holding an upvalue's value tells of the upvalue: the native
                // guard below checks both. See Note [Fragile information].
                if let Some(upvalue) = forced_mut.holds(idx) {
                    forced_mut.assume(Fragile::Upvalue { upvalue, ctype: idx_ctype.clone().unwrap() });
                }
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

    /// The thunk a call to R(A) of the context `calling`, continuing at
    /// `after`, ends its block in, or, not `appends`, a guard's failure is: run,
    /// it lays out a call for the function in R(A), guarding its identity and
    /// chaining a thunk for the next onto the guard's failure, while its chain
    /// guards fewer than `MAX_VERSIONS` (`identities`); past that, or for what
    /// isn't a function, a generic call. See Note [Call sites].
    fn make_call_thunk(&self, block_id: BlockId, calling: Rc<Context>, a: usize, b: usize, c: usize, after: BlockId, identities: usize, appends: bool) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            // In place, unless the thunk's JIT code can only be patched to a jump, or it
            // is a guard's failure, with the rest of the layout after it. See Note
            // [Thunk patching].
            let block = if !appends || vm.compiled(block_id) {
                let block = vm.new_block(vm.blocks[block_id.0].pc);
                vm.jump_thunk(block_id, thunk_pc, block);
                block
            } else {
                vm.blocks[block_id.0].instructions.truncate(thunk_pc);
                block_id
            };
            let (a16, b16, c16) = (a as u16, b as u16, c as u16);
            let next = |vm: &Specializer| Residual::Thunk(vm.make_call_thunk(block, calling.clone(), a, b, c, after, identities + 1, false));
            let mut layout = vec![];
            match state.vals[state.base + a].unbox() {
                LValue::LClosure(lclos) if matches!(calling.types[a], CType::LuaFunction(_)) || identities < MAX_VERSIONS => {
                    let proto = lclos.ro(owner).prototype;
                    if !matches!(calling.types[a], CType::LuaFunction(_)) {
                        layout.push(Residual::LuaGuard { idx: a, ptr: proto.cast() });
                        layout.push(next(vm));
                    }
                    let entry = Rc::new(entry_context(&calling, unsafe { &*proto }, a, b));
                    let (stack, vararg) = unsafe { ((*proto).max_stack, (*proto).is_vararg != 0) };
                    layout.push(Residual::LuaCall { entry: CallEntry::Context(entry), a: a16, b: b16, c: c16, stack, vararg });
                    layout.push(Residual::Arrive { a: a16, c: c16 });
                },
                LValue::NClosure(nf) if identities < MAX_VERSIONS => {
                    layout.push(Residual::NativeGuard { idx: a, ptr: nf.get_ptr() });
                    layout.push(next(vm));
                    // Past the guard the native is known: it runs as its window op if
                    // the call's arguments have the types the op assumes. See Note
                    // [Native windows].
                    let window = native_op(&calling, &nf, a, b, c)
                        .filter(|(end, op)| (a + 1..*end).all(|slot| op.args.accepts(&calling.slot(slot))));
                    if let Some((_, op)) = window {
                        layout.push(Residual::ExecWindow(op.window));
                        if c == 0 {
                            layout.push(Residual::ExecWindow(Rc::new(SetTop::new(a + 1, &[]))));
                        }
                    } else {
                        layout.push(Residual::NativeCall { nf: nf.native(), a: a16, b: b16, c: c16 });
                        // A native may allocate (a table, a string).
                        layout.push(Residual::GC);
                    }
                },
                _ => {
                    layout.push(Residual::Call { a: a16, b: b16, c: c16 });
                    layout.push(Residual::Arrive { a: a16, c: c16 });
                    // It may call a native, which may allocate.
                    layout.push(Residual::GC);
                },
            }
            layout.push(Residual::Jump(after));
            vm.blocks[block.0].instructions.extend(layout);
        })))
    }

    fn make_href_thunk(&self, mut block_id: BlockId, thunk_coro: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>, idx: usize, href: HashRef, pc: SubPc, mut thunk_ctx: Rc<Context>, appends: bool) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            let thunk_coro = thunk_coro.clone();
            let mut orig_ctx = thunk_ctx.clone();
            let thunk_mut = Rc::make_mut(&mut thunk_ctx);
            let hkey = &mut thunk_mut.hkeys[href.0 as usize];
            debug!("forcing href thunk for {idx} {href:?} {hkey:?}");
            let tab = state.table_at(idx);
            let Some((index, key, val)) = tab.ro(owner).hash.get_full(&LCanon::new((&hkey.key).into(), state.intern)) else {
                // The table doesn't have this key, which means we should actually just bailout
                let fail_block = vm.new_block(pc.0);
                if let Some((succ_next, succ_ty, succ_ret)) = vm.compile_one(owner, pc.next_false(), orig_ctx.clone(), thunk_coro, ResumeArg::Failed, fail_block) {
                    vm.compile(owner, succ_next, succ_ty, fail_block);
                }
                vm.jump_thunk(block_id, thunk_pc, fail_block);
                return;
            };
            debug!("href forced by {tab:?} -> {val:?}");
            // Its type is found out from the value loaded, in each table. See
            // Note [Field types].
            hkey.known_type = LType::Unknown;
            // Initialize the hkey after discovery with a cleared hazard for the index
            hkey.clear_checks();
            hkey.check(idx);

            // TODO: track the maximum number of hkeys + grow here instead so we can initialize the RunState
            // array.

            // The table's shape now has this hash key.
            if let CType::Shape(existing) = &mut thunk_mut.types[idx] {
                if !existing.contains(&href) {
                    existing.push(href)
                }
            } else {
                thunk_mut.types[idx] = CType::Shape(vec![href].into());
            }
            // The key's canonical form, made here once. See Note [Hash witnesses].
            let lkey = LCanon::constant(&hkey.key);
            let href_init = Residual::ExecWindow(Rc::new(HrefInit::new((index as u64) << 8 | href.0 as u64, lkey.boxed().bits(), &[idx])));
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

            let guard_block = vm.subblock(owner, pc.next_true(), thunk_ctx.clone(), thunk_coro.clone(), ResumeArg::HashRef(href, LType::Unknown));
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
            let expected = thunk_ctx.hkeys[href.0 as usize].known_type.clone();
            let update_href_thunk = vm.make_href_thunk(check_block, thunk_coro.clone(), tab, href.clone(), pc, thunk_ctx.clone(), false);
            // A field whose type isn't known has nothing to check it still has:
            // its hash key is found again. See Note [Field types].
            if expected == LType::Unknown {
                vm.blocks[check_block.0].instructions.push(Residual::Thunk(update_href_thunk));
                return;
            }
            let key = LCanon::constant(&thunk_ctx.hkeys[href.0 as usize].key).boxed().bits();
            vm.blocks[check_block.0].instructions.push(Residual::HashGuard { tab, href: href.clone(), key, expected });
            vm.blocks[check_block.0].instructions.push(Residual::Thunk(update_href_thunk));
            vm.blocks[check_block.0].instructions.push(Residual::Exec(ResidualExec::new("epoch_repair", Rc::new(move |owner, state| {
                // Re-init the witness and jump back to success block
                // The entry may have moved with the epoch: find its value again
                // by its index. See Note [Hash witnesses].
                let t = state.table_at(tab);
                let epoch = t.ro(owner).epoch;
                debug!("repairing {:?} epoch", href);
                let witness = &mut state.hash_witnesses[state.witness_base + href.0 as usize];
                let value = t.rw(owner).hash.get_index_mut(witness.index).unwrap().1 as *mut LBoxed<'_, '_>;
                witness.value = value.cast();
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
                CoroutineState::Yielded(YieldOp::NumberK(k)) => {
                    let proto = self.clos.ro(owner).prototype;
                    let crate::chunk::Constant::Number(n) = (unsafe { &(&(*proto).constants.items)[k] }) else { unreachable!() };
                    // Its NaN canonicalized, as boxing it would.
                    // See Note [Arithmetic NaNs].
                    arg = ResumeArg::Number(if n.0.is_nan() { f64::NAN } else { n.0 });
                },
                CoroutineState::Yielded(YieldOp::BoxedK(k)) => {
                    let proto = self.clos.ro(owner).prototype;
                    arg = ResumeArg::Boxed(LBoxed::from(unsafe { &(&(*proto).constants.items)[k] }).bits());
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
                    // we just didn't know, and if there is a runtime mismatch the next
                    // access's type guard finds it, as the store left the witness at the
                    // old epoch (`Retype::Unknown`).
                    let hkey = &mut Rc::make_mut(&mut ctx).hkeys[href.0 as usize];
                    if *ty != LType::Unknown {
                        hkey.known_type = *ty;
                    }
                    // If we updated an href, then we also need to set optimization hazards for any
                    // potentially aliased ones. We also need to invalidate this stack slot as
                    // well.
                    state = CoroutineState::Yielded(YieldOp::SetHazards(None, Some(href)));
                    arg = ResumeArg::Failed;
                    continue 'machine;
                },
                op @ CoroutineState::Yielded(YieldOp::HashKey(..) | YieldOp::TryHashKey(..)) => {
                    let proto = self.clos.ro(owner).prototype;
                    // The table's slot, the constant key, and whether to make a hash key
                    // if none exists yet.
                    let (place, k_const, allocate) = match op {
                        CoroutineState::Yielded(YieldOp::HashKey(idx, key)) => (idx, ((key & 0x100) != 0).then_some(key & 0xff), true),
                        CoroutineState::Yielded(YieldOp::TryHashKey(idx, key)) => (idx, ((key & 0x100) != 0).then_some(key & 0xff), false),
                        _ => unreachable!(),
                    };
                    // Only cache string keys
                    let Some(k_val) = k_const
                        .map(|k| unsafe { &(&(*proto).constants.items)[k] })
                        .filter(|k_val| matches!(k_val, crate::chunk::Constant::String(_)))
                    else {
                        pc = pc.next_false();
                        arg = ResumeArg::Failed;
                        break 'machine;
                    };
                    // The table's existing hash keys: its shape's.
                    let existing: SmallVec<[HashRef; 4]> = match &ctx.types[place] {
                        CType::Type(LType::Table) => SmallVec::new(),
                        CType::Shape(existing) => existing.clone(),
                        _ => panic!("HashKey should only be used on a table"),
                    };
                    debug!("hashkey on existing {existing:?}");
                    if let Some(cached) = existing.into_iter().find(|cached| &ctx.hkeys[cached.0 as usize].key == k_val) {
                        debug!("using cached href {:?}", cached);
                        let cached_hkey = &ctx.hkeys[cached.0 as usize];
                        // A cached href. Unless nothing could have invalidated it
                        // since it was last checked, it needs an epoch check first,
                        // which continues into blocks assuming it still holds.
                        arg = ResumeArg::HashRef(cached.clone(), cached_hkey.known_type.clone());
                        if cached_hkey.checked(place) {
                            // Nothing could have invalidated it: no check needed.
                            pc = pc.next_true();
                            debug!("using cached hkey without hazards");
                            break 'machine;
                        }
                        // After a passing epoch check, later accesses need no check
                        // until something may invalidate it again.
                        let mut holds_ctx = ctx.clone();
                        Rc::make_mut(&mut holds_ctx).hkeys[cached.0 as usize].check(place);
                        let holds_block = self.subblock(owner, pc.next_true(), holds_ctx.clone(), coro.clone(), arg);
                        self.make_epoch_check(owner, block_id, coro.clone(), place, cached.clone(), pc, ctx.clone(), holds_block);

                        self.end_block(block_id);
                        self.blocks[block_id.0].instructions.push(Residual::Jump(holds_block));
                        return None;
                    }
                    if !allocate {
                        pc = pc.next_false();
                        arg = ResumeArg::Failed;
                        break 'machine;
                    }
                    // We need these HashKeys to not have a lifetime, so that they can be
                    // captured by the generator: we only ever store the generator in the
                    // LClosure they came from, which is 'src 'lifetime, and so this is safe.
                    let k_val: &LConstant<'static, 'static> = unsafe { core::mem::transmute(k_val) };
                    // Try to find an orphaned HashKey slot to re-use
                    let href;
                    let orphan = ctx.hkeys.iter().enumerate().position(|(i, hkey)| hkey.orphan(HashRef(i as u8), &ctx.types));
                    if let Some(i) = orphan {
                        href = HashRef(i as u8);
                        Rc::make_mut(&mut ctx).hkeys[i] = HashKey::new(place, k_val.clone());
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
                    let witness = Residual::Thunk(self.make_href_thunk(block_id, thunk_coro, place, href.clone(), pc, thunk_ctx, true));
                    self.end_block(block_id);
                    self.blocks[block_id.0].instructions.push(witness);
                    return None;
                },
                CoroutineState::Yielded(YieldOp::GuardRk(rk, ref expected)) => {
                    let proto = self.clos.ro(owner).prototype;
                    if (rk & 0x100)!=0 {
                        let r_const = rk & (0xff);
                        let ty = constant_ctype(unsafe { &(&(*proto).constants.items)[r_const as usize] });
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
                        let proto = self.clos.ro(owner).prototype;
                        constant_ctype(unsafe { &(&(*proto).constants.items)[rk & 0xff] })
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
                        let thunk = Residual::Thunk(self.make_discovery_thunk(block_id, coro.clone(), rk, expected.clone(), None, pc, ctx.clone(), true, 0));
                        self.end_block(block_id);
                        self.blocks[block_id.0].instructions.push(thunk);
                        return None;
                    }
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
                        let thunk_coro = coro.clone();
                        let thunk_ctx = ctx.clone();
                        debug!("emitting discovery thunk");
                        let thunk = Residual::Thunk(self.make_discovery_thunk(block_id, thunk_coro, idx, CType::Type(expected), None, pc, thunk_ctx, true, 0));
                        self.end_block(block_id);
                        self.blocks[block_id.0].instructions.push(thunk);
                        return None;
                    }
                }
                CoroutineState::Yielded(YieldOp::Exec(func)) => {
                    self.blocks[block_id.0].instructions.push(Residual::Exec(func));
                    Rc::make_mut(&mut ctx).effect(Effect::WriteAny);
                },
                CoroutineState::Yielded(YieldOp::ExecWindow(w)) => {
                    for (&slot, access) in w.operands().iter().zip(w.accesses()) {
                        if access.writes() {
                            Rc::make_mut(&mut ctx).effect(Effect::Write(slot));
                        }
                    }
                    self.blocks[block_id.0].instructions.push(Residual::ExecWindow(w));
                },
                CoroutineState::Yielded(YieldOp::Effect(effect)) => {
                    Rc::make_mut(&mut ctx).effect(effect);
                },
                CoroutineState::Yielded(YieldOp::ArrayKind(table)) => {
                    arg = match ctx.array_kind(table) {
                        Some(kind) => ResumeArg::Type(CType::Type(kind)),
                        None => ResumeArg::Failed,
                    };
                },
                CoroutineState::Yielded(YieldOp::IsElementOf(slot, table)) => {
                    arg = if ctx.element_of(slot) == Some(table) { ResumeArg::Matched } else { ResumeArg::Failed };
                },
                CoroutineState::Yielded(YieldOp::ArrayType(slot, table)) => {
                    let kind = ctx.array_kind(table);
                    let ctx = Rc::make_mut(&mut ctx);
                    ctx.set_types(owner, vec![(slot, CType::Type(kind.unwrap_or(LType::Unknown)))]);
                    if kind.is_none() && slot != table {
                        ctx.assume(Fragile::ElementOf { slot, table });
                    }
                },
                CoroutineState::Yielded(YieldOp::FieldType(slot, href)) => {
                    let known = ctx.hkeys[href.0 as usize].known_type.clone();
                    Rc::make_mut(&mut ctx).set_types(owner, vec![(slot, CType::Type(known))]);
                    if known != LType::Unknown {
                        (pc, arg) = navigate(pc, &CType::Type(LType::Unknown), &CType::Type(known));
                    } else {
                        // Record the type on the hash key too, unless the load overwrote
                        // the table's register and dropped its hash keys.
                        let live = ctx.types.iter().any(|ctype| matches!(ctype, CType::Shape(hrefs) if hrefs.contains(&href)));
                        let thunk = Residual::Thunk(self.make_discovery_thunk(block_id, coro.clone(), slot, CType::Type(LType::Unknown), live.then_some(href), pc, ctx.clone(), true, 0));
                        self.end_block(block_id);
                        self.blocks[block_id.0].instructions.push(thunk);
                        return None;
                    }
                },
                CoroutineState::Yielded(YieldOp::LoadUpvalue(slot, upvalue)) => {
                    // See Note [Fragile information].
                    let known = ctx.upvalue(upvalue).cloned();
                    #[cfg(debug_assertions)]
                    if let Some(CType::NativeFunction(nf)) = &known {
                        // A native function the context assumes a slot holds: debug builds check it
                        // does. See Note [Fragile information].
                        windowed!(CheckNative, [native: usize], [], |owner, state, base| (value) {
                            let LValue::NClosure(nf) = value.unbox() else { panic!("fragile information: a native was assumed, {:?} found", value) };
                            assert_eq!(nf.get_ptr() as usize, native, "fragile information: another native was assumed");
                        });
                        self.blocks[block_id.0].instructions.push(Residual::ExecWindow(Rc::new(CheckNative::new(nf.get_ptr() as usize, &[slot]))));
                    }
                    let ctx = Rc::make_mut(&mut ctx);
                    ctx.set_types(owner, vec![(slot, known.unwrap_or(CType::Type(LType::Unknown)))]);
                    ctx.assume(Fragile::Holds { slot, upvalue });
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
                            // `result` here not only implies that we know the type of the result,
                            // but also that the operation is pure; we can treat it as not having
                            // any effects.
                            let mut result = None;
                            let calling = ctx.clone();
                            let native = matches!(ctx.types[a], CType::NativeFunction(_));
                            if let CType::NativeFunction(nf) = &ctx.types[a] {
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
                                } else {
                                    self.blocks[block_id.0].instructions.push(Residual::NativeCall {
                                        nf: nf.native(), a: a as u16, b: b as u16, c: c as u16
                                    });
                                    // A native may allocate (a table, a string).
                                    self.blocks[block_id.0].allocates = true;
                                }
                            }
                            // Any other call may run a closure, which reads and writes the
                            // slots it captured. See Note [Captured slots].
                            let captured = if result.is_none() {
                                captured_slots(unsafe { &*self.clos.ro(owner).prototype })
                            } else {
                                vec![]
                            };
                            if result.is_none() {
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
                                .map(|idx| (idx, CType::Type(LType::Unknown)))
                                .collect();
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
                                return Some((pc.0 + 1, ctx, ResumeArg::Start));
                            }
                            // Any other call ends its block in a thunk laying out the call
                            // for the function it finds, the code after it a version of
                            // its own. See Note [Call sites].
                            let after = if resumes {
                                self.subblock(owner, pc.next_true(), ctx, coro.clone(), ResumeArg::Start)
                            } else {
                                let after = self.jumping(owner, ctx, pc.0 + 1);
                                self.version(owner, pc.0 + 1, after)
                            };
                            self.end_block(block_id);
                            let thunk = self.make_call_thunk(block_id, calling, a, b, c, after, 0, true);
                            self.blocks[block_id.0].instructions.push(Residual::Thunk(thunk));
                            return None;
                        },
                    }
                },
                CoroutineState::Yielded(YieldOp::SetTypes(mut ty_effects)) => {
                    Rc::make_mut(&mut ctx).set_types(owner, ty_effects.drain(..).map(|(idx, ty)| (idx, CType::Type(ty))).collect())
                },
                CoroutineState::Yielded(YieldOp::GlobalCache(k)) => {
                    let proto = self.clos.ro(owner).prototype;
                    let key = LCanon::constant(unsafe { &(&(*proto).constants.items)[k] });
                    // A constant lives as long as its prototype, which the specializer's
                    // blocks do too.
                    let key: LCanon<'static, 'static> = unsafe { core::mem::transmute(key) };
                    let cache = Box::new(GlobalCache::new(key));
                    arg = ResumeArg::Cache(&*cache as *const GlobalCache);
                    self.global_caches.push(cache);
                },
                CoroutineState::Yielded(YieldOp::SetKeyHazards(k)) => {
                    let proto = self.clos.ro(owner).prototype;
                    let key: &LConstant<'static, 'static> = unsafe { core::mem::transmute(&(&(*proto).constants.items)[k]) };
                    Rc::make_mut(&mut ctx).set_key_hazards(key);
                },
                CoroutineState::Yielded(YieldOp::SetHazards(idx, href)) => {
                    Rc::make_mut(&mut ctx).set_hazards(idx, href)
                },
                CoroutineState::Yielded(YieldOp::Clobber(from)) => {
                    let clobbered = (from..ctx.types.len()).map(|idx| (idx, CType::Type(LType::Unknown))).collect();
                    Rc::make_mut(&mut ctx).set_types(owner, clobbered)
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
                    #[cfg(feature = "magic")]
                    if !state.force_jit.is_empty() {
                        self.force_jit(&mut state);
                    }
                    let next_off = (ret >> 32) as i32 as isize;
                    let next_id = (ret & 0xFFFFFFFF) as usize;
                    self.clos = state.clos.clone();

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
                Residual::Guard { idx, expected } | Residual::NumericGuard { idx, expected } => {
                    if expected.accepts(state.vals[state.base + idx].unbox().typeof_()) {
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
                    let hwit = state.hash_witnesses[state.witness_base + href.0 as usize];
                    let tab = state.table_at(tab);
                    warn!("epochcheck sees {} == {}", hwit.epoch, tab.ro(owner).epoch);
                    if hwit.epoch == tab.ro(owner).epoch {
                        // Fallthrough
                        off += 2;
                    } else {
                        off += 1;
                    }
                },
                Residual::HashGuard { tab, href, key, expected } => {
                    let hwit = state.hash_witnesses[state.witness_base + href.0 as usize];
                    let tab = state.table_at(tab);
                    let entry = tab.ro(owner).hash.get_index(hwit.index);
                    if entry.is_some_and(|(k, val)| k.boxed().bits() == key && expected.accepts(val.unbox().typeof_())) {
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
                    off += if state.select == 0 { 2 } else { 1 };
                },
                Residual::LuaCall { entry, a, b, c, stack, vararg } => {
                    let (caller, call) = (id, off);
                    off += 1;
                    state.call_lua(owner, Location(id, off).pack(), a, b);
                    // The closure called, which may be another of the prototype the
                    // guard checked.
                    let callee = state.clos.clone();
                    self.set_current(callee.clone());
                    let block = match entry {
                        CallEntry::Block(block) => block,
                        // Found now, once. See Note [Call sites].
                        CallEntry::Context(ctx) => {
                            self.versions.entry(callee.ro(owner).prototype).or_insert_with(|| HashMap::default());
                            let block = self.version(owner, 0, ctx);
                            self.set_current(callee.clone());
                            self.blocks[caller.0].instructions[call] = Residual::LuaCall { entry: CallEntry::Block(block), a, b, c, stack, vararg };
                            block
                        },
                    };
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
                        let next_stack = state.call_lua(owner, Location(id, off).pack(), a, b);
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
                        // Past the `Arrive`: the native put its results in place.
                        // See Note [Returns].
                        off += 1;
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
                Residual::Arrive { a, c } => {
                    off += 1;
                    state.arrive(a as usize, c as usize);
                },
                Residual::Ret(pc, a, b, closes, vararg) => {
                    debug!("spec final blocks: {:?}", self.blocks);
                    match state.leave(owner, a as usize, b as usize, closes, vararg) {
                        Ok(Location(block, disp)) => {
                            self.set_current(state.clos.clone());
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
        let reason = match off {
            -1 => "trap".to_string(),
            -2 => "return from the entry frame".to_string(),
            -3 => "select".to_string(),
            -4 => "thunk".to_string(),
            // A residual the JIT code doesn't run there, as a call to a function
            // with no code.
            off => format!("{}", self.blocks[block].instructions[off as usize]),
        };
        let (source, line) = Vm::info(state.clos.ro(owner).prototype);
        crate::tracing::instant("jit", "bailout", &[
            ("reason", reason.as_str().into()),
            ("block_id", block.into()),
            ("source", source.as_str().into()),
            ("line", (line as u64).into()),
        ]);
    }

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
                        Residual::Guard { .. } | Residual::NumericGuard { .. } | Residual::GuardDynamic(_) | Residual::HashGuard { .. } | Residual::NativeGuard { .. } | Residual::LuaGuard { .. } => {
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
