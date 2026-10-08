#![allow(unused_variables, unused_assignments, unused)]

use std::borrow::Cow;
use std::collections::HashMap;
use std::ops::{Coroutine, CoroutineState, Deref};
use std::pin::Pin;
use std::rc::Rc;
use std::cell::{Cell, RefCell};

use crate::vm::{CallstackEntry, HashWitness, NClosure, NativeFunc, Opcode, Location, Upvalue};
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
            Residual::Select(targets) => write!(f, "select"),
            Residual::Branch { .. } => write!(f, "branch"),
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
    OptimisticExec(Rc<dyn Window>), // An op with a cold path, which selects 0 on its hot path and
                                    // 1 on its cold. Resumed with Matched on the hot path, and
                                    // Failed on the cold. See Note [Optimistic ops]
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
    NarrowConstant(usize), // STACK[idx] is narrowed to an integer if a fact says it holds a
                           // whole constant, else left as it is. See Note [Narrowing]
    EncodeK(usize, usize), // STACK[idx] is about to be loaded with CONSTANT[k]: resumed with
                           // Matched to load it as an integer, Failed as a double whose fact
                           // isn't introduced, else as a double. See Note [Contraction]
    HoldsK(usize, usize), // STACK[idx] was just loaded with CONSTANT[k]. See Note [Narrowing]
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
    ArrayType(usize, usize), // Inform the executor that STACK[a] was loaded from STACK[b]'s array
                             // part: its type is the array's kind, if known. See Note [Array kinds]
    FieldType(usize, HashRef), // Inform the executor that STACK[idx]'s type is the same as an HREF's field.
                               // See Note [Field types]
    LoadUpvalue(usize, usize), // Infrom the executor that STACK[idx]'s type is the same as an UPVALUE[b].
                               // See Note [Fragile information]
    UpvalueKnown(usize), // Resumed with what the context knows of UPVALUE[idx]'s value: Boxed, the
                         // native it holds; else Integer, a stack slot holding it; else Failed.
                         // See Note [Fragile information]
    Effect(Effect), // An effect on fragile information the residuals yielded don't show. See
                    // Note [Fragile information]

    HashKey(usize, usize, bool), // Looks up or allocates an HREF for STACK[idx][key]; down its `__index` chain if true (a load). See Note [Table metatables]
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

/// How many `__index` hops down a table's chain a hash key's field can be.
/// See Note [Table metatables].
const MAX_CHAIN: usize = 3;

impl<'src, 'intern> HashKey<'src, 'intern> {
    fn tostring(&self, owner: &Owner) -> String {
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
    /// See Note [Global caches].
    Cache(*const GlobalCache),
    /// The end of a call's arguments, and the type its native's window op
    /// assumes they have.
    WindowArgs(usize, CType),
}

// Initialize a hash key: `at` is `index << 8 | href`. Its hot path finds the table's entry at
// `index` has the key `key` and the frame's witness for `href` has its place, populating the
// witness; its cold path finds the key wherever it is (`href_init_slow`). Exit 0 if the table has
// the key, where the field's type is guarded (`GuardWitness`), and 1 if not. See Notes [Hash
// witnesses] and [Field types].
windowed!(HrefInit, [at: u64, key: u64], [], |owner, state, base| (table) {
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
windowed!(select HrefInitIndex, [at: u64, key: u64], [], |owner, state, base| (userdata) {
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
windowed!(select HrefInitAt, [at: u64, key: u64, place: u16], [], |owner, state, base| () {
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
// and while any runs, the collector marks the whole stack (Note [Stack frames] in `vm`).
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

// `push_frame`, without the callstack's entry, for a call of R(A), with CALL's B (`a` and `b` as
// `Count::hold` holds them), of a callee whose `max_stack` is `stack`. Requires nilling the
// callee's frame if `FILLS`, or else the JIT code does. The callee isn't vararg. See Note [Frame
// ops].
windowed!(frame PushFrame, [a: u16, b: u16, stack: u8], [FILLS: bool, A: Count, B: Count], |owner, state, base| () {
    state.push_frame::<false>(owner, crate::vm::PackedLocation::from_bits(0), A.lift(a), B.lift(b), stack, FILLS);
    debug_assert!(unsafe { (*state.clos.ro(owner).prototype).is_vararg } == 0, "PushFrame of a vararg function's frame");
});

// `tail_call` for a tail call of R(A). `ab` is its `a | b << 16` (as `Count::hold` holds them);
// `effects` and `callee` the addresses of the running function's effects and the callee's, which
// the first is joined into (Note [Tail calls]). Closing upvalues if `CLOSES`, from a vararg
// function if `VARARG`. See Note [Frame ops].
windowed!(frame TailFrame, [ab: u64, effects: u64, callee: u64], [CLOSES: bool, VARARG: bool, A: Count, B: Count], |owner, state, base| () {
    let (a, b) = (A.lift(ab as u16), B.lift((ab >> 16) as u16));
    unsafe { *(callee as *mut u16) |= *(effects as *const u16) };
    state.tail_call(owner, a, b, CLOSES, VARARG);
});

// A `Ret` of R(A) and B (`a` and `b` as `Count::hold` holds them), returning `returns`, the id of
// what it returns (Note [Call continuations]), with its function's effects, at the address
// `effects` (Note [Call effects]); `at` (a `PackedLocation`) is where it is. Closing upvalues if
// `CLOSES`, returning from a vararg function if `VARARG`. A return from a frame JIT code called
// is the op; one from a frame with an entry, or the outermost, its cold path. See Note [Frame ops].
windowed!(frame PopFrame, [a: u16, b: u16, returns: u32, effects: u64, at: u64], [CLOSES: bool, VARARG: bool, A: Count, B: Count], |owner, state, base| () {
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

// Whether a table's array part has kind `kind`, testing an element loaded from it in place of
// the element's own tag. See Note [Array kinds].
windowed!(guard KindIs, [kind: LType], [], |owner, state, base| (table) {
    let LValue::Table(tab) = table.unbox() else { unreachable!() };
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
    Thunk(ThunkRef),
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
    /// context knows. Sizes the newly pushed frame to `stack` slots (the prototype's `max_stack`).
    /// `vararg` if the prototype is vararg (Note [Vararg frames]). See Note [Call sites].
    LuaCall { entry: CallEntry, a: u16, b: u16, c: u16, stack: u8, vararg: bool },
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
// A number is a double unless something narrows it to an integer, as LuaJIT narrows: a
// constant as a value (loaded, stored, passed) is a double whatever its value, as are a native's
// result and the generic paths' arithmetic. What narrows is a loop (below), a length, a bit
// operation, and a typed integer op on integers, until its result first overflows (Note
// [Optimistic ops]). A constant an i32 holds exactly is a compile-time
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
    (live..ctx.types.len()).any(|idx| forgotten(&ctx.types[idx]) || ctx.fragile.iter().any(|fact| !fact.survives(Effect::Write(idx))))
}

/// Forget, for a jump to a target where the registers from `live` on hold no
/// local, those registers' types and the fragile facts about them.
fn forget_dead(owner: &mut Owner, ctx: &mut Context, live: usize) {
    let dead = (live..ctx.types.len()).filter(|&idx| forgotten(&ctx.types[idx])).map(|idx| (idx, CType::Unknown)).collect();
    ctx.set_types(owner, dead);
    for idx in live..ctx.types.len() {
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
// and the rest compute on an integer. A slot a fact says holds a constant an i32 holds exactly (one
// `LOADK` loaded, until something writes the slot) is narrowed statically, the constant stored
// again in the integer encoding, at no cost each time the code runs: a counter a loop starts from a
// constant each time it is entered, even the first iteration computes on an integer. The fact is
// consumed by the slot's narrowing, whose type then says what it would, or by a guard finding out
// the slot's type at runtime, which decides how the slot is used instead (one the context answers
// decides nothing, as a loop's guards before narrowing); otherwise it holds until the slot is
// written. Where it is never used, the code it was carried through is contracted (Note
// [Contraction]). A slot holding such a constant is narrowed statically too where it escapes into
// an upvalue, captured by a closure or stored into one: a whole number kept there is most likely
// used as an integer, and is one for every reader. So is an argument of a native's window op (Note
// [Native windows] in `library`), which the op alone reads: the op then reads it as an integer, as
// it picks its form by which arguments are. A store into a table isn't narrowed: values reach a
// table's elements from many stores, constants stored from the constant table and copies among
// them, and narrowing only some would leave it holding both encodings.

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
// exist: those origins are queued for contraction. So too if the context's own facts the version
// lacks each say otherwise about something one of those facts is about, as a slot holding one
// constant on one path and another on the other: neither is worth keeping where they meet, and
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
// in `jit`): in place, truncating the dead residuals.
//
// A fact used for what it says can be rebuilt from the same origin the other way: a constant some
// code narrows to an integer (Note [Narrowing]) is loaded as an integer instead, so every path
// from its load computes on the integer, and none narrows it again. The narrowing still writes
// the integer until the rebuild, which waits and is dropped as a contraction is, but for the fact
// being used. An origin needn't introduce a fact: an integer op is rebuilt to compute in the
// double encoding once its result doesn't fit (Note [Optimistic ops]).
//
// Rebuilding replaces code, and the blocks only that code reached are then unreachable: nothing
// that runs (the code running, a frame returning, a handler, a rebuilt block) reaches them. JIT code is entered only
// as its block is, so it keeps alive only what it reaches when its block is reached. Versions are
// no roots, as only code that runs finds one again: versions reaching each other, as a caller's and
// the callee's it calls, are reached or not together. The unreachable ones are forgotten, as a
// contraction's are, once their point has all the versions it can have and needs the room: until
// then a path reaching one again, as a thunk forced into code that finds it, takes it as it is,
// with its JIT code. While code is
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
const MAX_VERSIONS: usize = 3;
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
    pub fragile: SmallVec<[Fact; 2]>,
}

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
// carry, read them unguarded.
//
// A guard finding out the representation of an element of a mixed array knows that too
// (a `Mixed` kind): it stays mixed however it is stored into, and a store into it needn't
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
// has none, and a call's continuation only what the callee's effects keep (Note [Call effects]).
//
// Effects come from the residuals as they are yielded (`Context::effect`). A window op writes the
// slots its accesses say it writes (`Effect::Write`), an exec may write any slot
// (`Effect::WriteAny`; it runs no Lua code), a call that isn't a window op or a pure native's
// (Note [Library natives] in `library`) is `Effect::Opaque`, and what a residual can't show a
// yield says (`YieldOp::Effect`: SETUPVAL's `Effect::SetUpvalue`). A store into a table is always yielded as one, `Effect::ArrayStore` or
// the hash hazards it sets, even where `WriteAny` already drops what it falsifies: an exec's
// `WriteAny` is of its own frame, and a caller sees only the store (Note [Call effects]).
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
// Instead the versions of a pc that differ only in their facts are kept ordered by inclusion, kind
// by kind of fact (`Fragile::class`), each one's facts of a kind a subset of the next's, and a
// context reaching the pc forgets whatever facts it has that would break that order. Dropping
// facts is always sound, since a version relying on fewer facts accepts any context with more, and
// n facts of a kind then give at most n + 1 versions for it. Kinds are kept apart so that facts of
// one kind, established and lost on their own schedule, never cost another kind's: a join of
// versions keeps a fact unless a version with facts of its kind lacks it.
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

/// Speculation the specializer assumes without a guard. See Note [Fragile
/// information].
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Fragile {
    /// Stack slot `slot` holds the value upvalue `upvalue` held when loaded
    /// into it.
    Holds { slot: usize, upvalue: usize },
    /// Upvalue `upvalue` holds a value of `ctype`, which a guard found in a
    /// slot holding its value: for a function past its identity guard, which.
    /// Every slot holding its value is of `ctype`.
    Upvalue { upvalue: usize, ctype: CType },
    /// Stack slot `slot` holds a value loaded from the array part of the table
    /// in slot `table`. See Note [Array kinds].
    ElementOf { slot: usize, table: usize },
    /// The array part of the table in slot `table` has kind `kind`. See Note
    /// [Array kinds].
    Kind { table: usize, kind: Kind },
    /// Stack slot `slot` holds a number constant an i32 holds exactly,
    /// `value`. See Note [Narrowing].
    Constant { slot: usize, value: i32 },
}

/// A fragile fact, with where the paths reaching it introduced it, if that can
/// be rebuilt without it. See Note [Contraction].
#[derive(Clone)]
pub struct Fact {
    pub fragile: Fragile,
    origins: Option<Origins>,
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

impl Fact {
    fn new(fragile: Fragile) -> Self {
        Self { fragile, origins: None }
    }
}

impl Deref for Fact {
    type Target = Fragile;
    fn deref(&self) -> &Fragile {
        &self.fragile
    }
}

// The origins are where a fact came from, not what it says: versions are
// told apart only by the fact.
impl PartialEq for Fact {
    fn eq(&self, other: &Fact) -> bool {
        self.fragile == other.fragile
    }
}

impl Eq for Fact {}

impl std::hash::Hash for Fact {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.fragile.hash(state)
    }
}

impl std::fmt::Debug for Fact {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fragile.fmt(f)
    }
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
}

impl Fragile {
    /// Its kind: facts of different kinds are kept apart where versions are
    /// told apart by their facts. See Note [Fragile information].
    fn class(&self) -> u8 {
        self.key().0
    }

    /// What the fact is about, unique among a context's facts, and their order.
    fn key(&self) -> (u8, usize) {
        match self {
            Fragile::Holds { slot, .. } => (0, *slot),
            Fragile::Upvalue { upvalue, .. } => (1, *upvalue),
            Fragile::ElementOf { slot, .. } => (2, *slot),
            Fragile::Kind { table, .. } => (3, *table),
            Fragile::Constant { slot, .. } => (4, *slot),
        }
    }

    /// Whether the fact still holds after `effect`.
    fn survives(&self, effect: Effect) -> bool {
        match (self, effect) {
            (_, Effect::Opaque) => false,
            (Fragile::Holds { slot, .. }, Effect::Write(written)) => written != *slot,
            (Fragile::Holds { .. }, Effect::WriteAny) => false,
            (Fragile::Holds { upvalue, .. } | Fragile::Upvalue { upvalue, .. }, Effect::SetUpvalue(set)) => set != *upvalue,
            (Fragile::Holds { .. } | Fragile::Upvalue { .. }, Effect::AnyUpvalue) => false,
            (Fragile::ElementOf { .. } | Fragile::Kind { .. }, Effect::AnyUpvalue) => true,
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
            (Fragile::Kind { kind, .. }, Effect::ArrayStore(stored)) => *kind == Kind::Mixed || stored.is_some_and(|stored| *kind == Kind::Of(stored)),
            // Only its slot holds it.
            (Fragile::Constant { slot, .. }, Effect::Write(written)) => written != *slot,
            (Fragile::Constant { .. }, Effect::WriteAny) => false,
            (Fragile::Constant { .. }, Effect::SetUpvalue(_) | Effect::AnyUpvalue | Effect::ArrayStore(_)) => true,
        }
    }
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Effects(pub u16);

impl Effects {
    pub const NONE: Effects = Effects(0);
    /// Some upvalue is set.
    pub const UPVALUE: Effects = Effects(1 << 8);
    /// Some table's hash part is stored into.
    pub const HASH: Effects = Effects(1 << 9);
    /// Code the specializer never saw ran: every other effect too.
    pub const OPAQUE: Effects = Effects(Self::ARRAYS | Self::UPVALUE.0 | Self::HASH.0 | Self::OPAQUE_BIT);
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
        for fact in &self.fragile {
            if let Fragile::Upvalue { ctype, .. } = &fact.fragile {
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
        self.introduce(Fact::new(fact));
    }

    /// Assume `fact`, as `assume`, with its origins.
    fn introduce(&mut self, fact: Fact) {
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
    fn array_kind(&self, table: usize) -> Option<Kind> {
        self.fragile.iter().find_map(|fact| match &fact.fragile {
            Fragile::Kind { table: known, kind } if *known == table => Some(*kind),
            _ => None,
        })
    }

    /// The slot of the table whose array part slot `slot`'s value was loaded
    /// from, if known. See Note [Array kinds].
    fn element_of(&self, slot: usize) -> Option<usize> {
        self.fragile.iter().find_map(|fact| match &fact.fragile {
            Fragile::ElementOf { slot: loaded, table } if *loaded == slot => Some(*table),
            _ => None,
        })
    }

    /// The upvalue whose value slot `slot` holds, if known.
    fn holds(&self, slot: usize) -> Option<usize> {
        self.fragile.iter().find_map(|fact| match &fact.fragile {
            Fragile::Holds { slot: held, upvalue } if *held == slot => Some(*upvalue),
            _ => None,
        })
    }

    /// Assume upvalue `upvalue` holds a value of `ctype`, as does each slot
    /// holding its value, unless the slot's type already tells more.
    fn learn_upvalue(&mut self, upvalue: usize, ctype: CType) {
        for fact in &self.fragile {
            if let Fragile::Holds { slot, upvalue: held } = fact.fragile && held == upvalue && self.types[slot].accepts(&ctype) {
                self.types[slot] = ctype.clone();
            }
        }
        self.assume(Fragile::Upvalue { upvalue, ctype });
    }

    /// A slot holding upvalue `upvalue`'s value, if one is known to.
    /// Slot `slot`'s type is found out at runtime: a fact that it holds a
    /// constant has had its use. See Note [Narrowing].
    fn used(&mut self, slot: usize) {
        self.fragile.retain(|fact| !matches!(fact.fragile, Fragile::Constant { slot: held, .. } if held == slot));
    }

    /// Mark that code relies on the fact about `key`, so that it isn't
    /// contracted. See Note [Contraction].
    fn rely(&self, owner: &mut Owner, key: (u8, usize)) {
        if let Some(origins) = self.fragile.iter().find(|fact| fact.key() == key).and_then(|fact| fact.origins.as_ref()) {
            for origin in owner.ro(origins).clone() {
                owner.rw(&origin).used = true;
            }
        }
    }

    /// Add the origins of `other`'s facts to those of the same facts of `self`,
    /// whose code `other`'s paths now reach. See Note [Contraction].
    fn adopt(&self, owner: &mut Owner, other: &Context) {
        for fact in &self.fragile {
            let Some(mine) = &fact.origins else { continue };
            let Some(theirs) = other.fragile.iter().find(|theirs| *theirs == fact).and_then(|theirs| theirs.origins.as_ref()) else { continue };
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
        self.fragile.iter().find_map(|fact| match &fact.fragile {
            Fragile::Constant { slot: held, value } if *held == slot => Some(*value),
            _ => None,
        })
    }

    fn held(&self, upvalue: usize) -> Option<usize> {
        self.fragile.iter().find_map(|fact| match &fact.fragile {
            Fragile::Holds { slot, upvalue: held } if *held == upvalue => Some(*slot),
            _ => None,
        })
    }

    /// The type of upvalue `upvalue`'s value, if known.
    fn upvalue(&self, upvalue: usize) -> Option<&CType> {
        self.fragile.iter().find_map(|fact| match &fact.fragile {
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
        self.types.get(idx).cloned().unwrap_or(CType::Unknown)
    }

    /// Whether a block specialized to `self` is correct in `other`. See Note
    /// [Version compatibility].
    fn accepts(&self, other: &Context) -> bool {
        self.hkeys.iter().enumerate().all(|(i, hkey)| {
            hkey.orphan() || other.hkeys.get(i).is_some_and(|theirs| hkey.accepts(theirs))
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

    /// Widen `self` to also accept `other`. Hash keys are joined one by one: a
    /// key both have at the same `HashRef`, of the same slot, stays, its field's
    /// type widened to both and checked only for the slots both check (a hazard
    /// either has, the join has). Any other is dropped: left an orphan, which
    /// `accepts` ignores, and forgotten by every shape listing it.
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
        // Kind by kind: a context with no fact of a kind doesn't drop that kind's.
        // See Note [Fragile information].
        self.fragile.retain(|fact| other.fragile.contains(fact) || !other.fragile.iter().any(|theirs| theirs.class() == fact.class()));
        for fact in self.fragile.iter_mut() {
            let theirs = other.fragile.iter().find(|theirs| *theirs == fact).and_then(|theirs| theirs.origins.as_ref());
            fact.origins = match (fact.origins.take(), theirs) {
                (Some(mine), Some(theirs)) => {
                    let mut origins = owner.ro(&mine).clone();
                    origins.extend(owner.ro(theirs).iter().filter(|origin| !owner.ro(&mine).iter().any(|known| Rc::ptr_eq(known, origin))).cloned());
                    Some(Rc::new(TLCell::new(origins)))
                },
                (mine, theirs) => mine.or_else(|| theirs.cloned()),
            };
        }
        let mut dropped: SmallVec<[HashRef; 8]> = SmallVec::new();
        for (i, mine) in self.hkeys.iter_mut().enumerate() {
            match other.hkeys.get(i) {
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
    pub clos: Tc<LClosure<'src, 'intern>>,
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
    /// Where each rebuilt block ends for code entering it from its start. See Note [Contraction].
    cuts: std::collections::HashMap<BlockId, usize, rustc_hash::FxBuildHasher>,
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
        for types in &self.returns {
            types.iter().for_each(|ty| ty.mark(owner));
        }
    }
}

impl<'src, 'intern> Specializer<'src, 'intern> {
    pub fn new(clos: Tc<LClosure<'src, 'intern>>) -> Self {
        Self {
            blocks: Vec::new(),
            global_caches: Vec::new(),
            versions: HashMap::default(),
            returns: Vec::new(),
            return_ids: HashMap::default(),
            effects: HashMap::default(),
            contractions: Vec::new(),
            encoding: None,
            cuts: Default::default(),
            trimming: Vec::new(),
            rebuilt: Default::default(),
            decided: Default::default(),
            unreachable: Default::default(),
            #[cfg(feature = "jit")]
            jctx: JitContext::new(),
            clos,
        }
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
        let cell = self.effects_of(self.clos.ro(owner).prototype);
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
        self.versions.get_mut(&self.clos.ro(owner).prototype).unwrap().insert((subpc, ctx.clone()), block_id);
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
        self.compile(owner, entry, ctx, block_id);
        return block_id;
    }

    pub fn subblock(&mut self, owner: &mut Owner, pc: SubPc, ctx: Rc<Context>, mut coro: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>, arg: ResumeArg) -> BlockId {
        if let Some(((_, ectx), &exists)) = self.versions.get(&self.clos.ro(owner).prototype).unwrap().get_key_value(&(pc, ctx.clone())) {
            ectx.clone().adopt(owner, &ctx);
            return exists;
        }
        let ctx = self.contractible(owner, pc, ctx);
        if let Some(((_, ectx), &exists)) = self.versions.get(&self.clos.ro(owner).prototype).unwrap().get_key_value(&(pc, ctx.clone())) {
            ectx.clone().adopt(owner, &ctx);
            return exists;
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
        let versions = self.versions.get(&self.clos.ro(owner).prototype).unwrap();
        if let Some(((_, ectx), &exists)) = versions.get_key_value(&(subpc, ctx.clone())) {
            ectx.clone().adopt(owner, &ctx);
            self.unreachable.remove(&exists);
            return (exists, "exact", None);
        }
        let ctx = self.contractible(owner, subpc, ctx);
        let versions = self.versions.get(&self.clos.ro(owner).prototype).unwrap();
        if let Some(((_, ectx), &exists)) = versions.get_key_value(&(subpc, ctx.clone())) {
            ectx.clone().adopt(owner, &ctx);
            self.unreachable.remove(&exists);
            return (exists, "exact", None);
        }
        if self.versions_at(owner, subpc) >= MAX_VERSIONS {
            self.evict(owner, subpc);
        }
        let versions = self.versions.get(&self.clos.ro(owner).prototype).unwrap();
        let existing: Vec<(Rc<Context>, BlockId)> = versions
            .iter()
            .filter(|((epc, _), _)| *epc == subpc)
            .map(|((_, ectx), block)| (ectx.clone(), *block))
            .collect();
        // Versions differing only in fragile information are, kind by kind of
        // fact, a chain of subsets, each version's facts of the kind in the
        // next's: `ctx` keeps the most facts of each kind that keep it one. See
        // Note [Fragile information].
        let alike: Vec<&(Rc<Context>, BlockId)> = existing.iter().filter(|(ectx, _)| ectx.alike(&ctx)).collect();
        let mut classes: SmallVec<[u8; 8]> = alike.iter().flat_map(|(ectx, _)| ectx.fragile.iter()).chain(ctx.fragile.iter()).map(|fact| fact.class()).collect();
        classes.sort_unstable();
        classes.dedup();
        let mut kept: Vec<Fact> = Vec::new();
        for class in classes {
            let of = |facts: &[Fact]| facts.iter().filter(|fact| fact.class() == class).cloned().collect::<Vec<_>>();
            let mine = of(&ctx.fragile);
            let mut chain: Vec<Vec<Fact>> = alike.iter().map(|(ectx, _)| of(&ectx.fragile)).collect();
            chain.sort_by_key(Vec::len);
            chain.dedup();
            let below = chain.iter().rposition(|facts| facts.iter().all(|fact| mine.contains(fact)));
            // Above the top every fact is kept; otherwise those shared with the
            // version above the highest `ctx` has all of, or with the bottom.
            match below.map_or(chain.first(), |below| chain.get(below + 1)) {
                Some(above) => kept.extend(mine.into_iter().filter(|fact| above.contains(fact))),
                None => kept.extend(mine),
            }
        }
        let ctx = if kept.len() == ctx.fragile.len() {
            ctx
        } else {
            let mut lowered = (*ctx).clone();
            lowered.fragile.retain(|fact| kept.contains(fact));
            if let Some((ectx, block)) = alike.iter().find(|(ectx, _)| ectx.fragile == lowered.fragile) {
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

    /// How many versions the running function has at `pc`.
    fn versions_at(&self, owner: &Owner, pc: SubPc) -> usize {
        self.versions.get(&self.clos.ro(owner).prototype).map_or(0, |versions| versions.keys().filter(|(at, _)| *at == pc).count())
    }

    /// Forget the versions at `pc` of the running function the trimming found unreachable, which
    /// a point with all the versions it can have needs the room of. See Note [Contraction].
    fn evict(&mut self, owner: &Owner, pc: SubPc) {
        let unreachable = &mut self.unreachable;
        let mut _evicted: Vec<usize> = Vec::new();
        self.versions.get_mut(&self.clos.ro(owner).prototype).unwrap().retain(|(at, _), block| {
            let evict = *at == pc && unreachable.remove(block);
            if evict {
                _evicted.push(block.0);
            }
            !evict
        });
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
        let proto = self.clos.ro(owner).prototype;
        let mut origins: Vec<Origin> = Vec::new();
        let mut _duplicates: Vec<usize> = Vec::new();
        for (ectx, block) in existing {
            let mut extra = ectx.fragile.iter().filter(|fact| !joined.fragile.contains(fact)).peekable();
            if extra.peek().is_none() {
                continue;
            }
            let Some(sets) = extra.map(|fact| fact.origins.as_ref()).collect::<Option<Vec<_>>>() else { continue };
            let found: Vec<Origin> = sets.iter().flat_map(|set| owner.ro(set).iter().cloned()).collect();
            if found.iter().any(|origin| owner.ro(origin).used) || found.iter().all(|origin| owner.ro(origin).rebuild.is_none()) {
                continue;
            }
            _duplicates.push(block.0);
            for origin in found {
                if !origins.iter().any(|known| Rc::ptr_eq(known, &origin)) {
                    origins.push(origin);
                }
            }
        }
        let queued = |origin: &Origin| self.contractions.iter().any(|(_, queued, _)| queued.iter().any(|known| Rc::ptr_eq(known, origin)));
        if origins.is_empty() || origins.iter().all(queued) {
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
        let proto = self.clos.ro(owner).prototype;
        let mut origins: Vec<Origin> = Vec::new();
        let mut conflicting: SmallVec<[(u8, usize); 2]> = SmallVec::new();
        let mut _duplicates: Vec<usize> = Vec::new();
        for ((epc, ectx), _block) in self.versions.get(&proto).unwrap() {
            if *epc != pc {
                continue;
            }
            // A version whose slot holding a constant holds another type here: the constant is
            // worth nothing past the point either. See Note [Contraction].
            if !ectx.alike(&ctx) {
                let retyped = ectx.fragile.iter().filter(|fact| {
                    matches!(fact.fragile, Fragile::Constant { slot, .. } if !ctx.fragile.contains(fact) && ectx.slot(slot) != ctx.slot(slot))
                });
                let Some(sets) = retyped.map(|fact| fact.origins.as_ref()).collect::<Option<Vec<_>>>() else { continue };
                let found: Vec<Origin> = sets.iter().flat_map(|set| owner.ro(set).iter().cloned()).collect();
                if found.is_empty() || found.iter().any(|origin| owner.ro(origin).used) || found.iter().all(|origin| owner.ro(origin).rebuild.is_none()) {
                    continue;
                }
                _duplicates.push(_block.0);
                for origin in found {
                    if !origins.iter().any(|known| Rc::ptr_eq(known, &origin)) {
                        origins.push(origin);
                    }
                }
                continue;
            }
            // `ctx`'s facts the version lacks each contradict one of its own.
            let mine: SmallVec<[(u8, usize); 2]> = ctx.fragile.iter().filter(|fact| !ectx.fragile.contains(fact)).map(|fact| fact.key()).collect();
            if !mine.iter().all(|key| ectx.fragile.iter().any(|theirs| theirs.key() == *key)) {
                continue;
            }
            let mut extra = ectx.fragile.iter().filter(|fact| !ctx.fragile.contains(fact)).peekable();
            if extra.peek().is_none() {
                continue;
            }
            let Some(sets) = extra.map(|fact| fact.origins.as_ref()).collect::<Option<Vec<_>>>() else { continue };
            let found: Vec<Origin> = sets.iter().flat_map(|set| owner.ro(set).iter().cloned()).collect();
            if found.iter().any(|origin| owner.ro(origin).used) || found.iter().all(|origin| owner.ro(origin).rebuild.is_none()) {
                continue;
            }
            _duplicates.push(_block.0);
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
        if !origins.is_empty() && !origins.iter().all(queued) {
            #[cfg(feature = "tracing")]
            {
                let context = ctx.tostring(owner);
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
        if conflicting.is_empty() {
            return ctx;
        }
        let mut lowered = (*ctx).clone();
        lowered.fragile.retain(|fact| !conflicting.contains(&fact.key()));
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
        self.decided.get(&self.clos.ro(owner).prototype)?.get(&pc).cloned()
    }

    /// Rebuild the queued origins of the running function that nothing runs past, the interpreter
    /// at `at` or a frame returning: each becomes a thunk compiling the code from there again, and
    /// the blocks the code it replaced reached are to be trimmed. See Note [Contraction].
    fn rebuild_queued(&mut self, owner: &mut Owner, state: &RunState<'src, 'intern>, at: &Location) {
        let proto = self.clos.ro(owner).prototype;
        for (of, origins, how) in std::mem::take(&mut self.contractions) {
            if of != proto {
                self.contractions.push((of, origins, how));
                continue;
            }
            let _blocks = Self::ids(origins.iter().map(|origin| owner.ro(origin).block.0));
            let _how = match how {
                ResumeArg::Matched => "integer",
                ResumeArg::Failed => "drop",
                _ => "double",
            };
            // Relied on since (which an integer serves as well), or rebuilt in code
            // that has its own JIT code.
            let refused = if how == ResumeArg::Failed && origins.iter().any(|origin| owner.ro(origin).used) {
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
            if live.iter().any(|origin| past(owner.ro(origin), at) || state.callstack.iter().any(|entry| past(owner.ro(origin), &entry.ret))) {
                #[cfg(feature = "tracing")]
                crate::tracing::instant("spec", "contract_deferred", &[
                    ("line", self.traced_line(owner).into()),
                    ("origins", _blocks.as_str().into()),
                    ("at", at.0.0.into()),
                ]);
                self.contractions.push((of, origins, how));
                continue;
            }
            let carries = |ctx: &Context| ctx.fragile.iter().any(|fact| {
                fact.origins.as_ref().is_some_and(|set| owner.ro(set).iter().any(|origin| origins.iter().any(|known| Rc::ptr_eq(known, origin))))
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

    /// The residuals of `block` that code entering it at `from` runs: from there to its end, or to
    /// a rebuild's jump in it if `from` is before that. See Note [Contraction].
    fn runnable(&self, block: BlockId, from: usize) -> &[Residual] {
        let residuals = &self.blocks[block.0].instructions;
        let end = match self.cuts.get(&block) {
            Some(&cut) if from < cut => cut.min(residuals.len()),
            _ => residuals.len(),
        };
        &residuals[from.min(end)..end]
    }

    /// The blocks `residuals` can go on to.
    fn targets(residuals: &[Residual]) -> impl Iterator<Item = BlockId> + '_ {
        residuals.iter().flat_map(|residual| -> SmallVec<[BlockId; 2]> {
            match residual {
                Residual::Jump(target) => smallvec::smallvec![*target],
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
            .chain(state.callstack.iter().map(|entry| (entry.ret.0, entry.ret.1)))
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

    /// `ids` as a comma separated list, for traces.
    fn ids(ids: impl Iterator<Item = usize>) -> String {
        ids.map(|id| id.to_string()).collect::<Vec<_>>().join(",")
    }

    /// The source line of the function being specialized, for traces.
    #[cfg(feature = "tracing")]
    fn traced_line(&self, owner: &Owner) -> u64 {
        Vm::info(self.clos.ro(owner).prototype).1 as u64
    }

    /// `version`'s choice, for the trace (`spec`/`version`, see
    /// `tools/trace_sql.py`): with how many versions `pc` has after it, and
    /// how many of the requested context's shapes the join lost.
    #[cfg(feature = "tracing")]
    fn trace_version(&self, owner: &Owner, pc: Pc, requested: &Context, block: BlockId, outcome: &str, joined: Option<&Context>) {
        let versions = self.versions.get(&self.clos.ro(owner).prototype).map_or(0, |v| v.keys().filter(|(epc, _)| *epc == SubPc::new(pc)).count());
        let context = requested.tostring(owner);
        let joined_context = joined.map(|j| j.tostring(owner)).unwrap_or_default();
        let shapes_dropped = joined.map_or(0, |j| {
            (0..requested.types.len()).filter(|&i| matches!(requested.types[i], CType::Shape(..)) && !matches!(j.slot(i), CType::Shape(..))).count()
        });
        let origins = requested.fragile.iter().map(|fact| {
            let from = fact.origins.as_ref().map(|set| owner.ro(set).iter().map(|origin| format!("{}@{}", owner.ro(origin).block.0, owner.ro(origin).offset)).collect::<Vec<_>>().join(","));
            format!("{:?} <- {}", fact.fragile, from.unwrap_or_default())
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
    /// names, as a thunk's layout), pc, context, residuals and, with the JIT,
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
            let mut args: Vec<(&str, crate::tracing::TraceValue)> = vec![
                ("block", id.into()),
                ("line", lines.get(&BlockId(id)).copied().unwrap_or(0).into()),
                ("pc", block.pc.into()),
                ("residuals", block.instructions.len().into()),
                ("context", context.as_str().into()),
                ("returns", returns.as_str().into()),
                ("returned_from", returned_from.as_str().into()),
                ("unreachable", (self.unreachable.contains(&BlockId(id)) as u64).into()),
            ];
            #[cfg(feature = "jit")]
            {
                args.push(("hotness", block.jit_info.hotness.get().into()));
                args.push(("jitted", (block.jit_info.entry.is_some() as u64).into()));
            }
            crate::tracing::instant("spec", "block_summary", &args);
        }
    }

    /// Return a specialized block for a given PC and context, compiling a new one if necessary
    pub fn find(&mut self, owner: &mut Owner, pc: SubPc, ctx: &Rc<Context>) -> Option<BlockId>
    {
        self.versions.get(&self.clos.ro(owner).prototype).unwrap().get(&(pc, ctx.clone())).cloned()
    }

    pub fn compile(&mut self, owner: &mut Owner, mut pc: Pc, mut ctx: Rc<Context>, block_id: BlockId) -> Rc<Context> {
        loop {
            let inst = unsafe { self.clos.ro(owner).prototype.as_ref().unwrap().instructions.items[pc].clone() };
            // Only a call uses the top the instruction before left. See Note [Known top].
            if ctx.top.is_some() && !matches!(inst.0.Opcode(), Opcode::CALL | Opcode::TAILCALL) {
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
                Opcode::TAILCALL => {
                    let (a, b) = crate::vm::AB::unpack(inst.0);
                    self.end_block(block_id);
                    let proto = self.clos.ro(owner).prototype;
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
                    let proto = unsafe { &*self.clos.ro(owner).prototype };
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
                    self.blocks[block_id.0].instructions.push(Residual::Ret(pc, a, b, closes, proto.is_vararg != 0, returns, effects)); None
                },
                x => {
                    #[cfg(debug_assertions)]
                    {
                        unreachable!("{:?}", x)
                    }
                    panic!("{:?}", x);
                    let proto = self.clos.ro(owner).prototype;
                    let vararg = unsafe { (*proto).is_vararg != 0 };
                    let effects: *const Cell<Effects> = self.effects_of(proto);
                    self.blocks[block_id.0].instructions.push(Residual::Ret(pc, 0, 0, true, vararg, UNKNOWN_RETURN, effects)); None
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
        let typed = |fact: &Fact| matches!(fact.fragile, Fragile::ElementOf { slot, .. } if ctx.slot(slot) != CType::Unknown);
        if ctx.fragile.iter().any(typed) {
            let forgotten: Vec<Fact> = ctx.fragile.iter().filter(|fact| typed(fact)).cloned().collect();
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

    /// A `GuardDynamic`'s side not yet taken, compiled and jumped to in its
    /// place when first taken. See Note [Dynamic guards].
    /// The thunk a `Narrow` of `slot`, a double, ends its block in. See Note
    /// [Narrowing].
    fn make_narrow_thunk(&self, block_id: BlockId, thunk_coro: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>, slot: usize, pc: SubPc, thunk_ctx: Rc<Context>) -> ThunkRef {
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

    /// Narrow slot `slot` of `block`, a double, statically if a fact says it holds a
    /// whole constant: the constant is stored again in the integer encoding. Whether
    /// it was. See Note [Narrowing].
    fn narrow_constant(&mut self, owner: &mut Owner, ctx: &mut Rc<Context>, slot: usize, block: BlockId) -> bool {
        let Some(value) = ctx.constant(slot) else { return false };
        let key = Fragile::Constant { slot, value }.key();
        ctx.rely(owner, key);
        // Rebuilt from where the constant was loaded, as an integer. See Note
        // [Contraction].
        if let Some(set) = ctx.fragile.iter().find(|fact| fact.key() == key).and_then(|fact| fact.origins.as_ref()) {
            let origins: Vec<Origin> = owner.ro(set).iter().filter(|origin| owner.ro(origin).rebuild.is_some()).cloned().collect();
            let queued = |origin: &Origin| self.contractions.iter().any(|(_, queued, _)| queued.iter().any(|known| Rc::ptr_eq(known, origin)));
            let queues = !origins.is_empty() && !origins.iter().all(queued);
            #[cfg(feature = "tracing")]
            crate::tracing::instant("spec", "narrow", &[
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
                self.contractions.push((self.clos.ro(owner).prototype, origins, ResumeArg::Matched));
            }
        }
        self.blocks[block.0].instructions.push(Residual::ExecWindow(Rc::new(crate::generators::NarrowK::new(value, &[slot]))));
        // The fact used, and dropped by the write: its type says what it would, so
        // no version keeps it apart.
        let ctx = Rc::make_mut(ctx);
        ctx.effect(Effect::Write(slot));
        ctx.set_types(owner, vec![(slot, CType::Type(LType::Integer))]);
        true
    }

    /// Where the yield of `coro` at `pc` in `ctx` introduces a fact: rebuilding
    /// truncates `block` there and resumes `coro` in `ctx`, without the fact.
    /// See Note [Contraction].
    fn origin(&self, block: BlockId, coro: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>, pc: SubPc, ctx: Rc<Context>) -> Origin {
        let offset = self.blocks[block.0].instructions.len();
        // The origin becomes a thunk laying out the rebuilt code. See Note [Contraction].
        let rebuild = move |vm: &mut Specializer, owner: &mut Owner, how: ResumeArg| {
            let thunk = ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
                // In place, unless the thunk's JIT code can only be patched to a jump (Note [Thunk
                // patching] in `jit`). Nothing returns into the residuals after it, which it
                // truncates: the rebuild waited until nothing ran past it.
                assert!(!state.callstack.iter().any(|entry| entry.ret.0 == block && entry.ret.1 > thunk_pc), "a frame returns past a rebuilt origin");
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
                if let Some((next, ctx, _)) = vm.compile_one(owner, pc, ctx.clone(), coro.clone(), how.clone(), at) {
                    vm.compile(owner, next, ctx, at);
                }
            })));
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
    fn make_encoding_thunk(&self, block_id: BlockId, thunk_coro: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>, pc: SubPc, thunk_ctx: Rc<Context>, fits: Fits) -> ThunkRef {
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
            if let Some((next, ctx, _)) = vm.compile_one(owner, pc, thunk_ctx.clone(), thunk_coro.clone(), answer, at) {
                vm.compile(owner, next, ctx, at);
            }
            vm.encoding = None;
        })))
    }

    /// An optimistic op's cold way, as `make_side_thunk`'s, which the first time it's taken also
    /// queues where the op's encoding was asked, if anywhere, to be rebuilt computing it in the
    /// double encoding. See Note [Optimistic ops].
    fn make_overflow_thunk(&self, block_id: BlockId, thunk_coro: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>, pc: SubPc, thunk_ctx: Rc<Context>, asked: Option<Origin>) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            let side = vm.subblock(owner, pc, thunk_ctx.clone(), thunk_coro.clone(), ResumeArg::Failed);
            vm.jump_thunk(block_id, thunk_pc, side);
            if !overflow_rebuilds() {
                return;
            }
            let Some(origin) = asked.clone().filter(|origin| owner.ro(origin).rebuild.is_some()) else { return };
            let queued = vm.contractions.iter().any(|(_, queued, _)| queued.iter().any(|known| Rc::ptr_eq(known, &origin)));
            if !queued {
                vm.contractions.push((vm.clos.ro(owner).prototype, vec![origin], ResumeArg::Type(CType::Type(LType::Double))));
            }
        })))
    }

    fn make_side_thunk(&self, block_id: BlockId, thunk_coro: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>, pc: SubPc, thunk_ctx: Rc<Context>, arg: ResumeArg) -> ThunkRef {
        ThunkRef(Rc::new(RefCell::new(move |vm: &mut Specializer, owner: &mut Owner, state: &mut RunState, thunk_pc: usize| {
            let side = vm.subblock(owner, pc, thunk_ctx.clone(), thunk_coro.clone(), arg.clone());
            vm.jump_thunk(block_id, thunk_pc, side);
        })))
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
    fn make_discovery_thunk(&self, block_id: BlockId, thunk_coro: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>, idx: usize, expected: CType, field: Option<HashRef>, pc: SubPc, mut thunk_ctx: Rc<Context>, appends: bool, identities: usize) -> ThunkRef {

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
                forced_mut.assume(Fragile::Kind { table, kind: Kind::Of(found_field) });
            }
            // An array of two representations or more stays mixed.
            if let Some((table, _)) = array.filter(|&(_, kind)| kind.count_ones() > 1) {
                forced_mut.assume(Fragile::Kind { table, kind: Kind::Mixed });
            }
            // A slot holding an upvalue's value tells of the upvalue: the type the
            // guard found, and past a function's identity guard below, which
            // function. See Note [Fragile information].
            if let Some(href) = field {
                forced_mut.hkeys[href.0 as usize].known_type = Some(Kind::Of(found_field));
            }
            let holds = forced_mut.holds(idx);
            if let Some(upvalue) = holds {
                forced_mut.learn_upvalue(upvalue, found.clone());
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
                if let Some(upvalue) = holds {
                    forced_mut.learn_upvalue(upvalue, idx_ctype.clone().unwrap());
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
                if let Some(upvalue) = holds {
                    forced_mut.learn_upvalue(upvalue, idx_ctype.clone().unwrap());
                }
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
    /// `after` (as `After::block`), ends its block in, or, not `appends`, a guard's failure is: run,
    /// it lays out a call for the function in R(A), guarding its identity and
    /// chaining a thunk for the next onto the guard's failure, while its chain
    /// guards fewer than `MAX_VERSIONS` (`identities`); past that, or for what
    /// isn't a function, a generic call. With a `continuation`, the context
    /// before the call less the callee's frame, the caller's captured slots
    /// below it, and the pc after it, a Lua function's call continues at a thunk
    /// specializing it to the return. See Notes [Call sites], [Call
    /// continuations] and [Call effects].
    fn make_call_thunk(&self, block_id: BlockId, calling: Rc<Context>, pc: SubPc, a: usize, b: usize, c: usize, after: After, continuation: Option<(Rc<Context>, Rc<[usize]>, Pc)>, identities: usize, appends: bool) -> ThunkRef {
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
            let next = |vm: &Specializer| Residual::Thunk(vm.make_call_thunk(block, calling.clone(), pc, a, b, c, after.clone(), continuation.clone(), identities + 1, false));
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
                    if let Some((ctx, captured, pc)) = &continuation {
                        // See Note [Call continuations].
                        layout.push(Residual::Thunk(vm.make_continuation_thunk(block, ctx.clone(), captured.clone(), *pc, a, c, after.clone(), 0, true)));
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
                    layout.push(next(vm));
                    let after = after.block(vm, owner);
                    layout.extend(Self::protected_call(a, b, c, after));
                    layout.push(Residual::Jump(after));
                    vm.blocks[block.0].instructions.extend(layout);
                    vm.join_effects(owner, Effects::OPAQUE);
                    return;
                },
                LValue::NClosure(nf) if identities < MAX_VERSIONS => {
                    layout.push(Residual::NativeGuard { idx: a, ptr: nf.get_ptr() });
                    layout.push(next(vm));
                    // Past the guard, a native with a generator is compiled by it, as an opcode is,
                    // and the code after the call is a version. See Note [Native generators] in
                    // `library`.
                    if let (Some(generator), After::Version(..)) = (nf.generator(), &after) {
                        vm.blocks[block.0].instructions.extend(layout);
                        let coro = Box::new(generator(nf.native(), a, b, c));
                        if let Some((next, ctx, _)) = vm.compile_one(owner, pc, calling.clone(), coro, ResumeArg::Start, block) {
                            let ctx = vm.jumping(owner, ctx, next);
                            let version = After::Version(next, ctx).block(vm, owner);
                            vm.blocks[block.0].instructions.push(Residual::Jump(version));
                        }
                        return;
                    }
                    // Past the guard the native is known: it runs as its window op if
                    // the call's arguments have the types the op assumes. See Note
                    // [Native windows].
                    let window = native_op(&calling, &nf, a, b, c)
                        .filter(|(end, op)| (a + 1..*end).all(|slot| op.args.accepts(&calling.slot(slot))));
                    // What the code after an effect-free call knows: its context before the
                    // call, but for the callee's frame, and a window op's result.
                    let mut known = continuation.as_ref().map(|(before, _, pc)| ((**before).clone(), *pc));
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
                    if let Some((known, pc)) = known {
                        let known = vm.jumping(owner, Rc::new(known), pc);
                        layout.push(Residual::Jump(After::Version(pc, known).block(vm, owner)));
                        vm.blocks[block.0].instructions.extend(layout);
                        return;
                    }
                },
                _ => {
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
    fn make_continuation_thunk(&self, block_id: BlockId, ctx: Rc<Context>, captured: Rc<[usize]>, pc: Pc, a: usize, c: usize, after: After, identities: usize, appends: bool) -> ThunkRef {
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
                    let version = vm.version(owner, pc, Rc::new(known));
                    layout.push(Residual::ReturnedFrom(returned));
                    layout.push(Residual::Thunk(vm.make_continuation_thunk(block, ctx.clone(), captured.clone(), pc, a, c, after.clone(), identities + 1, false)));
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
    fn make_href_thunk(&self, block_id: BlockId, thunk_coro: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>, idx: usize, href: HashRef, pc: SubPc, thunk_ctx: Rc<Context>, appends: bool, chains: bool, next: Option<HashRef>, fail_ctx: Rc<Context>) -> ThunkRef {
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
                if let Some((succ_next, succ_ty, _)) = vm.compile_one(owner, pc.next_false(), fail_ctx.clone(), thunk_coro, ResumeArg::Failed, fail_block) {
                    vm.compile(owner, succ_next, succ_ty, fail_block);
                }
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
    fn guard_witness(&mut self, owner: &mut Owner, block: BlockId, thunk_coro: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>, idx: usize, href: HashRef, expected: LType, pc: SubPc, ctx: Rc<Context>, chains: bool, next: Option<HashRef>, fail_ctx: Rc<Context>) {
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

    fn make_epoch_check(&mut self, owner: &mut Owner, block_id: BlockId, thunk_coro: Box<impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static>, tab: usize, href: HashRef, pc: SubPc, thunk_ctx: Rc<Context>, success_block: BlockId, chains: bool) {
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

    pub fn compile_one<C>(&mut self, owner: &mut Owner, mut pc: SubPc, mut ctx: Rc<Context>, mut coro: Box<C>, mut arg: ResumeArg, block_id: BlockId) -> Option<(Pc, Rc<Context>, ResumeArg)>
    where C: Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static
    {
        // Where the constant being loaded was, for its fact's origin.
        let mut loading: Option<Origin> = None;
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
                CoroutineState::Yielded(YieldOp::IntegralK(k)) => {
                    let proto = self.clos.ro(owner).prototype;
                    arg = if integral_constant(unsafe { &(&(*proto).constants.items)[k] }) { ResumeArg::Matched } else { ResumeArg::Failed };
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
                    let proto = self.clos.ro(owner).prototype;
                    let constant = unsafe { &(&(*proto).constants.items)[k] };
                    arg = if matches!(constant, crate::chunk::Constant::String(s) if s.as_bytes() == name) { ResumeArg::Matched } else { ResumeArg::Failed };
                },
                CoroutineState::Yielded(YieldOp::HashKey(place, key, chains)) => {
                    let proto = self.clos.ro(owner).prototype;
                    // The constant key.
                    let k_const = ((key & 0x100) != 0).then_some(key & 0xff);
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
                    // Try to find an orphaned HashKey slot to re-use
                    let href;
                    let orphan = ctx.hkeys.iter().enumerate().position(|(_, hkey)| hkey.orphan());
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
                    let witness = Residual::Thunk(self.make_href_thunk(block_id, thunk_coro, place, href.clone(), pc, thunk_ctx.clone(), true, chains, None, thunk_ctx));
                    self.end_block(block_id);
                    self.blocks[block_id.0].instructions.push(witness);
                    return None;
                },
                CoroutineState::Yielded(YieldOp::GuardRk(rk, ref expected)) => {
                    let proto = self.clos.ro(owner).prototype;
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
                        let proto = self.clos.ro(owner).prototype;
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
                        // See Note [Narrowing].
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
                CoroutineState::Yielded(YieldOp::Encoding(fits)) => {
                    // Decided by its operands the first time it runs. See Note [Optimistic ops].
                    let thunk = Residual::Thunk(self.make_encoding_thunk(block_id, coro.clone(), pc, ctx.clone(), fits));
                    self.end_block(block_id);
                    self.blocks[block_id.0].instructions.push(thunk);
                    return None;
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
                        // See Note [Narrowing].
                        Rc::make_mut(&mut ctx).used(idx);
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
                    arg = if ctx.element_of(slot) == Some(table) { ResumeArg::Matched } else { ResumeArg::Failed };
                },
                CoroutineState::Yielded(YieldOp::ArrayType(slot, table)) => {
                    let kind = ctx.array_kind(table);
                    let ctx = Rc::make_mut(&mut ctx);
                    ctx.set_types(owner, vec![(slot, kind.map_or(CType::Unknown, Kind::ctype))]);
                    if kind.is_none() && slot != table {
                        ctx.assume(Fragile::ElementOf { slot, table });
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
                            windowed!(CheckLua, [proto: usize], [], |owner, state, base| (value) {
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
                                let coro = Box::new(generator(nf.native(), a, b, c));
                                return self.compile_one(owner, pc, ctx, coro, ResumeArg::Start, block_id);
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
                                captured_slots(unsafe { &*self.clos.ro(owner).prototype })
                            } else {
                                vec![]
                            };
                            // For a Lua callee's continuation, which applies only what the
                            // callee's effects falsify: the context before the call, but for
                            // the callee's frame, from `a` on. See Note [Call effects].
                            let before = (!native).then(|| {
                                let mut before = (*ctx).clone();
                                for idx in a..before.types.len() {
                                    before.effect(Effect::Write(idx));
                                }
                                let frame = (a..before.types.len()).map(|idx| (idx, CType::Unknown)).collect();
                                before.set_types(owner, frame);
                                let captured: Rc<[usize]> = captured.iter().copied().filter(|&slot| slot < a).collect();
                                (Rc::new(before), captured)
                            });
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
                                return Some((pc.0 + 1, ctx, ResumeArg::Start));
                            }
                            // Any other call ends its block in a thunk laying out the call
                            // for the function it finds, the code after it a version of
                            // its own. See Note [Call sites].
                            let (after, continuation) = if resumes {
                                (After::Block(self.subblock(owner, pc.next_true(), ctx, coro.clone(), ResumeArg::Start)), None)
                            } else {
                                // A Lua callee's return also chooses a version of its own. See
                                // Note [Call continuations].
                                let continuation = before.map(|(before, captured)| (before, captured, pc.0 + 1));
                                let after = self.jumping(owner, ctx, pc.0 + 1);
                                (After::Version(pc.0 + 1, after), continuation)
                            };
                            self.end_block(block_id);
                            let thunk = self.make_call_thunk(block_id, calling, pc, a, b, c, after, continuation, 0, true);
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
                    Rc::make_mut(&mut ctx).set_types(owner, clobbered)
                },
                CoroutineState::Yielded(YieldOp::NarrowConstant(slot)) => {
                    if ctx.types.get(slot) == Some(&CType::Type(LType::Double)) {
                        self.narrow_constant(owner, &mut ctx, slot, block_id);
                    }
                },
                CoroutineState::Yielded(YieldOp::EncodeK(..)) if let Some(how) = self.decision(owner, pc) => {
                    arg = how;
                },
                CoroutineState::Yielded(YieldOp::EncodeK(_, k)) => {
                    let proto = self.clos.ro(owner).prototype;
                    if let crate::chunk::Constant::Number(n) = unsafe { &(&(*proto).constants.items)[k] } && is_integer(n.0) {
                        loading = Some(self.origin(block_id, coro.clone(), pc, ctx.clone()));
                    }
                },
                CoroutineState::Yielded(YieldOp::HoldsK(slot, k)) => {
                    let proto = self.clos.ro(owner).prototype;
                    if let crate::chunk::Constant::Number(n) = unsafe { &(&(*proto).constants.items)[k] } && is_integer(n.0) {
                        let origin = loading.take().expect("a constant's load yields EncodeK first");
                        Rc::make_mut(&mut ctx).introduce(Fact { fragile: Fragile::Constant { slot, value: n.0 as i32 }, origins: Some(Rc::new(TLCell::new(vec![origin]))) });
                    }
                },
                CoroutineState::Yielded(YieldOp::Narrow(slot)) => match ctx.types[slot].clone() {
                    CType::Type(LType::Integer) => {
                        pc = pc.next_true();
                        arg = ResumeArg::Matched;
                    }
                    CType::Type(LType::Double) if self.narrow_constant(owner, &mut ctx, slot, block_id) => {
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
                        self.jit_compile(id, owner);
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
                &Residual::LuaCall { ref entry, a, b, c, stack, vararg } => {
                    let entry = entry.clone();
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
                &Residual::TailCall { ref entry, a, b, closes, vararg, effects, callee_effects } => {
                    let entry = entry.clone();
                    let (caller, call) = (id, off);
                    // What the tail caller did, the callee's return must tell. See Note
                    // [Tail calls].
                    unsafe { (*callee_effects).set((*callee_effects).get().join((*effects).get())) };
                    state.tail_call(owner, a as usize, b as usize, closes, vararg);
                    let callee = state.clos.clone();
                    self.set_current(callee.clone());
                    let block = match entry {
                        CallEntry::Block(block) => block,
                        // Found now, once. See Note [Call sites].
                        CallEntry::Context(ctx) => {
                            self.versions.entry(callee.ro(owner).prototype).or_insert_with(|| HashMap::default());
                            let block = self.version(owner, 0, ctx);
                            self.set_current(callee.clone());
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
                        // See Note [Errors].
                        let name = String::from_utf8_lossy(crate::library::type_name(state.vals[state.base + a as usize]));
                        state.raise(LBoxed::box_lvalue(LValue::OwnedString(crate::gc::Gc::string(format!("attempt to call a {name} value").as_bytes()))));
                    }
                },
                &Residual::Jump(target) => {
                    id = target;
                    off = 0;
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
                    match state.leave::<true>(owner, a as usize, b as usize, closes, vararg) {
                        // The interpreter runs no frame JIT code called: each has its entry.
                        Ok(None) => unreachable!("a return from a frame with no entry in the interpreter"),
                        Ok(Some(Location(block, disp))) => {
                            // See Note [Call continuations].
                            let effects = unsafe { (*effects).get() }.0 as u64;
                            state.returned = crate::vm::RETURNED | effects << crate::vm::EFFECTS_SHIFT | returns as u64;
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
            // The call's function's frame starts where the frame above its own
            // entry was called from, or is the running one.
            let callee = state.callstack.get(handler.depth + 1).map_or(state.base, |entry| entry.frame);
            state.close_upvalues_from(owner, callee);
            let entry = &state.callstack[handler.depth];
            let (clos, frame, witness_frame, witness_top) = (entry.clos.clone(), entry.frame, entry.witness_frame, entry.witness_top);
            state.callstack.truncate(handler.depth);
            state.clos = clos;
            state.base = frame;
            state.witness_base = witness_frame;
            state.witness_top = witness_top;
        }
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
        self.set_current(state.clos.clone());
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
                        Residual::Guard { .. } | Residual::NumericGuard { .. } | Residual::GuardDynamic(_) | Residual::HashGuard { .. } | Residual::GuardWitness { .. } | Residual::NativeGuard { .. } | Residual::LuaGuard { .. } => {
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
                        Residual::Branch { hot, cold } => {
                            edges.push(Stmt::Edge(edge!(node_id!(block_id) => node_id!(hot.0); attr!("label", "hot"))));
                            edges.push(Stmt::Edge(edge!(node_id!(block_id) => node_id!(cold.0); attr!("label", "cold"))));
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
