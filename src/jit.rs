#![allow(unused_parens)]
use std::io::Write;
use std::rc::Rc;
use std::cell::Cell;
use std::collections::{HashMap, BTreeMap};
use crate::{Owner, TLCell, TlcOwner};
use crate::vm::{BlockId, HashWitness, LBoxed, LClosure, LType, LValue, PackedLocation, Location, RunState, Tc, Vm, Witnesses};
use crate::gc::{GcInner, GcCtx};
use crate::lboxed::NClosureCell;
use crate::stack::ValueStack;
use crate::specialize::{Block, CallEntry, CType, Context, Residual, Specializer, SubPc};
use crate::window::{stencil_body, Access, Body, Captures, Image, NextRef, StencilError, Window, EXITS, WINDOW};
use crate::window_alloc::{plan_trace, Cache, ALLOCATED, Emit, Packed, Placement, Rise, Step, WindowAlloc, SCRATCH};
use crate::trace::{Block as TraceBlock, Event, Loops, Policy, Region, Slots};
use dynasmrt::relocations::{Relocation, RelocationKind, RelocationSize};
use dynasmrt::{AssemblyOffset, DynamicLabel, DynasmApi, DynasmLabelApi, ExecutableBuffer, dynasm};
use smallvec::SmallVec;
use rustc_hash::FxBuildHasher;

use log::debug;
use log::info;
use log::warn;

#[cfg(feature = "unreachable")]
#[macro_use]
use crate::unreachable;

#[cfg(feature = "immediate_jit")]
const INITIAL_HOTNESS: usize = 0;
#[cfg(not(feature = "immediate_jit"))]
const INITIAL_HOTNESS: usize = 64;

#[derive(Debug)]
pub struct JitInfo {
    pub buffer: Option<ExecutableBuffer>,
    pub entry: Option<JitExec>,
    pub hotness: std::cell::Cell<usize>,
}

impl JitInfo {
    pub fn new() -> Self {
        JitInfo {
            buffer: None,
            entry: None,
            hotness: Cell::new(INITIAL_HOTNESS),
        }
    }
}

pub type JitExec = for<'a, 'src, 'intern> extern "rust-preserve-none" fn(&'a mut RunState<'src, 'intern>, *const LBoxed<'src, 'intern>) -> u64;

pub fn get_ptr_from_closure(f: &dyn for <'a, 'b, 'src, 'intern> Fn(&mut Owner, &'b mut RunState<'src, 'intern>)) -> (*const (), usize, usize) {
    let (addr, meta) = (f as *const dyn for <'a, 'b, 'src, 'intern> Fn(&mut Owner, &'b mut RunState<'src, 'intern>)).to_raw_parts();
    #[derive(Debug)]
    #[repr(C)]
    struct RawMeta {
        vtable: &'static [usize; 8],
    }
    unsafe {
        let vtable = std::mem::transmute::<_, RawMeta>(meta);
        let call = vtable.vtable[4];
        return (addr, vtable.vtable as &_ as *const _ as usize, call);
    }
}

// Note [Thunk patching]
// ~~~~~~~~~~~~~~~~~~~~~
// A thunk compiled into JIT code exits to the interpreter, which forces it,
// but forcing rewrites residuals, not JIT code: a thunk forced after its block
// was compiled would exit there every time, and a side exit taken often would
// run through the interpreter on every pass.
//
// So a thunk's JIT code starts with five bytes of nops (`NOP5`), room for a
// `jmp rel32`, before it stores the window's dirty registers and exits; the
// site keeps the window the thunk leaves. Forcing a thunk in a block with JIT
// code leaves a jump where it was, whatever guard it adds starting a new block,
// and every thunk made a jump goes through `jump_thunk`, which links its site
// to the target: now if the target has JIT code, else once it does. Linking
// makes the nops a jump to the site's own compensation code, the transfer a
// compiled jump would do from the thunk's window to the target's entry window
// (a value both keep in a register is neither stored nor loaded), then a jump
// into the target: the path stays in JIT code from then on.
//
// A target compiled with a thunk waiting to be linked into it, the thunk whose
// path got it hot, plans its region from that thunk's window: it is the hint
// its entry window starts from (see Note [Trace allocation] in
// `window_alloc`).

// Note [Snapshots]
// ~~~~~~~~~~~~~~~~
// Flushing the window, storing its dirty registers to their slots, is data:
// which registers go to which slots. A snapshot is that data, and the location
// of the flush, as an entry of the region's pool; a flush through one is a call
// with the snapshot's address in rax to the `flush_snapshot` all regions share,
// which does the stores, sets `current_off` to the location's offset, and
// returns with every register as it was. It is code only to find its data, but
// slower than the stores inline: saving the window and looping over the stores
// costs more than the stores do, so a flush on a path that runs often stays
// inline.
//
// An exit, which runs rarely, flushes through a snapshot: a thunk is only its
// `NOP5` and a jump, with its snapshot's address in rax, to the shared
// `exit_snapshot`, which flushes through the snapshot and exits the region
// trapping at the snapshot's location.
//
// rax is free for the address: as `SCRATCH` it holds no value between moves.
//
// A store of an unboxed register names its XMM half, which `flush_snapshot`
// saves next to the general registers and boxes as it stores it. See Note
// [Unboxed doubles] in `window_alloc`.

/// A five-byte nop: the room a thunk site leaves for a `jmp rel32`.
const NOP5: [u8; 5] = [0x0f, 0x1f, 0x44, 0x00, 0x00];

/// The address the JIT passes as an `&mut Owner` argument: the token is
/// zero-sized, so any non-null aligned address is one. See `crate::forge_owner`.
const FORGED_OWNER: i64 = core::mem::align_of::<Owner>() as i64;

pub struct JitHelper;
impl JitHelper {
    pub unsafe extern "C" fn check_guard(state: *mut (), idx: usize, expected: LType) -> bool {
        unsafe {
            //println!("state {:?} idx {} {}", state, idx, expected);
            let state = state as *mut RunState;
            let rs = &*state;
            let val = &rs.vals[rs.base + idx];
            val.unbox().typeof_() == expected
        }
    }
    pub unsafe extern "C" fn check_epoch(state: *mut (), tab: usize, href: u8, place: u16) -> bool {
        unsafe {
            //println!("state {:?} {} {}", state, tab, href);
            let state = state as *mut RunState;
            // Forge an owner
            let mut owner = ();
            let owner = (&raw mut owner as *mut Owner).as_ref_unchecked();
            let rs = &*state;
            rs.witness_holds(owner, tab, crate::vm::Place::from_bits(place), href)
        }
    }
    pub unsafe extern "C" fn check_hash_guard(state: *mut (), tab: usize, href: u8, expected: LType, key: u64) -> bool {
        unsafe {
            let state = state as *mut RunState;
            // Forge an owner
            let mut owner = ();
            let owner = (&raw mut owner as *mut Owner).as_ref_unchecked();
            let rs = &*state;
            rs.witness_entry_holds(owner, tab, href, key, expected)
        }
    }

    /// Run a window op whose stencil the copier rejected, through its
    /// interpreter path: operands from their stack homes, outputs flushed.
    pub unsafe extern "C" fn window_interp(state: *mut (), op: *const (), vtable: *const ()) {
        unsafe {
            let op: *const dyn Window = core::ptr::from_raw_parts(op, core::mem::transmute(vtable));
            let owner = crate::forge_owner();
            let state = &mut *(state as *mut RunState<'static, 'static>);
            (*op).interp(owner, state);
        }
    }

    /// Incremental GC safepoint from JIT'd code. The roots (state + specializer)
    /// were published before entering the JIT and the value stack is mutated in
    /// place, so `step_published` traces the live state. See Note [GC roots].
    pub unsafe extern "C" fn gc_safepoint() {
        unsafe {
            let owner = crate::forge_owner();
            GcCtx::assume_rooted().step_published(owner);
        }
    }

    /// A call from JIT code to whatever slot `a` holds.
    /// * A native is called and returns `1`.
    /// * A Lua function who has JIT code has a frame pushed, and returns the function pointer.
    /// * Anything else (a function not compiled yet, a `__call`) returns 0 and should cause a
    ///   bailout for the interpreter to call.
    pub unsafe extern "C" fn dynamic_call(spec: *mut (), state: *mut (), ret: u64, a: u16, b: u16, c: u16) -> usize {
        unsafe {
            let spec = &mut *(spec as *mut Specializer<'static, 'static>);
            let state = &mut *(state as *mut RunState<'static, 'static>);
            let owner = crate::forge_owner();
            match state.vals[state.base + a as usize].unbox() {
                LValue::NClosure(ncall) => {
                    state.call_native(ncall.native(), a, b, c, owner);
                    1
                }
                // Inside frames JIT code called, the interpreter makes the call, once the callstack
                // is whole. See Note [Frame ops] in `specialize`.
                LValue::LClosure(_) if state.jit_depth > 0 => 0,
                LValue::LClosure(lclos) => {
                    let Some(entry) = spec.lua_entry(owner, &lclos) else { return 0 };
                    let ret = PackedLocation::from_bits(ret as usize);
                    state.call_lua(owner, ret, a, b);
                    entry as usize
                }
                _ => 0,
            }
        }
    }

    /// The entry of the frame a call from JIT code made, which a bailout is unwinding, from what
    /// the call kept on the native stack at `kept` (the frame's caller's hash witnesses' top and
    /// base, base, and closure, in that order up the stack) and its return location `ret`. Gives
    /// back the bailout's `exit`, for the call to leave with. See Note [Frame ops] in `specialize`.
    pub unsafe extern "C" fn unwind_frame(state: *mut (), kept: *const u64, ret: u64, exit: u64) -> u64 {
        unsafe {
            let state = &mut *(state as *mut RunState<'static, 'static>);
            let kept = core::slice::from_raw_parts(kept, 4);
            let clos = crate::vm::Tc(crate::gc::Gc::from_addr(kept[3]));
            state.unwind_jit_frame(clos, kept[2] as usize, kept[1] as usize, kept[0] as usize, PackedLocation::from_bits(ret as usize));
            exit
        }
    }

    /// Raise `error`, a native's, called from JIT code. See Note [Errors] in
    /// `specialize`.
    pub unsafe extern "C" fn raise(state: *mut (), error: u64) {
        unsafe {
            let state = &mut *(state as *mut RunState<'static, 'static>);
            state.raise(LBoxed::from_bits(error));
        }
    }

    /// A call from JIT code of the native `nf` taking every result, through
    /// `call_native`: there may be more than the call's slots.
    pub unsafe extern "C" fn native_call(state: *mut (), nf: usize, a: u16, b: u16) {
        unsafe {
            let state = &mut *(state as *mut RunState<'static, 'static>);
            let nf: crate::vm::NativeFunc = core::mem::transmute(nf);
            state.call_native(nf, a, b, 0, crate::forge_owner());
        }
    }

    /// A `LuaCall` from JIT code compiled before its callee's version had code,
    /// until the site is linked to it (Note [Call linking]), or whose version it
    /// hadn't found: the version's code if it has some now, its frame pushed,
    /// else as `dynamic_call`. `ret` names the call, as the residual before it.
    /// See Note [Call sites].
    pub unsafe extern "C" fn lua_call(spec: *mut (), state: *mut (), ret: u64, a: u16, b: u16, c: u16) -> usize {
        unsafe {
            let specializer = &mut *(spec as *mut Specializer<'static, 'static>);
            let Location(BlockId(block), after) = Location::unpack(PackedLocation::from_bits(ret as usize));
            let call = after - 1;
            if let Residual::LuaCall { entry: CallEntry::Block(entry), .. } = &specializer.blocks[block].instructions[call] {
                if let Some(code) = specializer.blocks[entry.0].jit_info.entry {
                    let state = &mut *(state as *mut RunState<'static, 'static>);
                    // As `dynamic_call`'s. See Note [Frame ops] in `specialize`.
                    if state.jit_depth > 0 {
                        return 0;
                    }
                    let owner = crate::forge_owner();
                    state.call_lua(owner, PackedLocation::from_bits(ret as usize), a, b);
                    return code as usize;
                }
            }
            Self::dynamic_call(spec, state, ret, a, b, c)
        }
    }
}

type Assembler = dynasmrt::VecAssembler::<dynasmrt::x64::X64Relocation>;

/// Write a line to `window_dump.txt` (feature `window_dump`, `just
/// window-dump`): each compiled block's window allocation.
macro_rules! window_dump {
    ($jctx:expr, $($arg:tt)*) => {
        #[cfg(feature = "window_dump")]
        if let Some(dump) = &$jctx.window_dump {
            writeln!(dump.borrow_mut(), $($arg)*).ok();
        }
    };
}

/// Note what the code `$ops` assembles next is, for the disassembly (feature
/// `jit_disasm`).
macro_rules! jit_note {
    ($jctx:expr, $ops:expr, $($arg:tt)*) => {
        #[cfg(feature = "jit_disasm")]
        $jctx.disasm.note($ops.offset().0, format!($($arg)*));
    };
}

/// Allocator code as one line, for `window_dump!`.
#[cfg(feature = "window_dump")]
fn emits_line(emits: &[Emit]) -> String {
    emits.iter().map(ToString::to_string).collect::<Vec<_>>().join("; ")
}

/// Count how often the allocator code emitted next runs (feature `window_dump`):
/// ` #id`, for its dump line, of a counter incremented just before it, whose
/// total the dump ends with. Nothing for no code. Clobbers rax and the flags.
macro_rules! window_count {
    ($jctx:expr, $ops:expr, $emits:expr) => {{
        #[cfg(feature = "window_dump")]
        let id = if $emits.is_empty() { String::new() } else { format!(" #{}", window_count(&$jctx.window_counts, $ops)) };
        #[cfg(not(feature = "window_dump"))]
        let id = "";
        id
    }};
}

/// For code laid out elsewhere, `window_count!` without the count: its id in
/// the dump, and the counter's address for that code's `emit_count`.
macro_rules! window_deferred {
    ($jctx:expr, $emits:expr) => {{
        #[cfg(feature = "window_dump")]
        let counted = if $emits.is_empty() {
            (String::new(), None)
        } else {
            let (id, at) = window_counter(&$jctx.window_counts);
            (format!(" #{id}"), Some(at))
        };
        #[cfg(not(feature = "window_dump"))]
        let counted: (&str, Option<i64>) = ("", None);
        counted
    }};
}

/// A new window dump counter: its id, and its address.
#[cfg(feature = "window_dump")]
fn window_counter(counts: &std::cell::RefCell<Vec<Box<std::sync::atomic::AtomicU64>>>) -> (usize, i64) {
    let mut counts = counts.borrow_mut();
    let counter = Box::new(std::sync::atomic::AtomicU64::new(0));
    let at = counter.as_ptr() as i64;
    counts.push(counter);
    (counts.len() - 1, at)
}

#[cfg(feature = "window_dump")]
fn window_count(counts: &std::cell::RefCell<Vec<Box<std::sync::atomic::AtomicU64>>>, ops: &mut Assembler) -> usize {
    let (id, at) = window_counter(counts);
    emit_count(ops, at);
    id
}

/// Count one more run of the code here on the window dump counter at `at`.
fn emit_count(ops: &mut Assembler, at: i64) {
    dynasm!(ops
        ; .arch x64
        ; mov rax, QWORD at
        ; inc QWORD [rax]
    );
}

/// The window registers `w0..w7` in the order the stencil ABI passes them (the
/// `rust-preserve-none` arguments after state, base and the pinned tag in r12,
/// r13, r14), then `SCRATCH`: rax, which every stencil clobbers (LLVM loads its
/// `become` target into it), so it only holds a value within one sequence of
/// moves.
const WINDOW_REGS: [u8; WINDOW + 1] = [
    15, /* r15 */ 7, /* rdi */ 6, /* rsi */ 2, /* rdx */ 1, /* rcx */
    8, /* r8 */ 9, /* r9 */ 11, /* r11 */ 0, /* rax */
];

/// An entry of the pool emitted after a compiled region's code, a multiple of 8
/// bytes.
enum PoolEntry {
    Value(u64),
    /// The absolute address of a label.
    Address(DynamicLabel),
    /// A window flush. See Note [Snapshots].
    Snapshot(Snapshot),
    /// A site's record: the absolute address of where each of its exits goes,
    /// then the displacement from the record to each capture's value entry, as
    /// an `i32`. See Note [Cold stencils] in `window`.
    /// With the op's name and captures, for disassembly.
    Record([DynamicLabel; EXITS], SmallVec<[DynamicLabel; 4]>, &'static str, Captures),
}

/// A window flush, which `flush_snapshot` does. See Note [Snapshots].
struct Snapshot {
    /// Where the flush is.
    location: PackedLocation,
    /// The window register index, whether its value is unboxed, and slot of
    /// each store.
    stores: Vec<(usize, bool, usize)>,
}

impl Snapshot {
    /// Its pool bytes: `location`, the store count as a `u32`, then a `u16`
    /// slot and `u16` register index for each store, padded to 8 bytes. The
    /// index of a register's XMM half is `WINDOW` past its own.
    fn bytes(&self) -> Vec<u8> {
        let mut bytes = (self.location.bits() as u64).to_le_bytes().to_vec();
        bytes.extend(u32::try_from(self.stores.len()).unwrap().to_le_bytes());
        for &(reg, unboxed, slot) in &self.stores {
            bytes.extend(u16::try_from(slot).expect("a slot in a u16").to_le_bytes());
            bytes.extend(u16::try_from(reg + if unboxed { WINDOW } else { 0 }).unwrap().to_le_bytes());
        }
        bytes.resize(bytes.len().next_multiple_of(8), 0);
        bytes
    }
}

/// The pool of a compiled region: its entries in order, each equal value once;
/// and its code off every hot path, laid out after its blocks.
#[derive(Default)]
struct Pool {
    entries: Vec<(DynamicLabel, PoolEntry)>,
    values: HashMap<u64, DynamicLabel, FxBuildHasher>,
    stubs: Vec<(DynamicLabel, Stub)>,
}

/// Code a region lays out after its blocks, off its hot paths.
enum Stub {
    /// The way from a copy into its cold stencil: the site's record's address
    /// into `cold_site`, then the jump. See Note [Cold stencils] in `window`.
    ColdEntry { record: DynamicLabel, cold: usize },
    /// The way an op's exit takes, off the hot path, to a target of the
    /// `Select` or `Branch` after it: out of its copy's alignment if `aligned`,
    /// the window's moves, then the jump. See Note [Window exits] in `window`.
    /// With `count`, the window dump's counter of its moves.
    Way { aligned: bool, moves: SmallVec<[Emit; 16]>, to: JumpTo, count: Option<i64> },
    /// An exit of an op that selects with no `Select` or `Branch` after it:
    /// out of its copy's alignment if `aligned`, the exit to `select`, then on
    /// at `join`. See Note [Window exits] in `window`.
    Select { aligned: bool, exit: usize, join: DynamicLabel },
}

/// Where a jump to a block goes: its code, or a label it will have.
enum JumpTo {
    Code(usize),
    Label(DynamicLabel),
}

impl Pool {
    /// The label of an entry holding `value`.
    fn value(&mut self, ops: &mut Assembler, value: u64) -> DynamicLabel {
        *self.values.entry(value).or_insert_with(|| {
            let label = ops.new_dynamic_label();
            self.entries.push((label, PoolEntry::Value(value)));
            label
        })
    }

    /// The label of a new entry holding the absolute address of `target`.
    fn address(&mut self, ops: &mut Assembler, target: DynamicLabel) -> DynamicLabel {
        let label = ops.new_dynamic_label();
        self.entries.push((label, PoolEntry::Address(target)));
        label
    }

    /// The label of a new entry holding the record of a site whose exits go
    /// to `exits`, with `captures`. See Note [Cold stencils] in `window`.
    fn record(&mut self, ops: &mut Assembler, exits: [DynamicLabel; EXITS], name: &'static str, captures: &Captures) -> DynamicLabel {
        let values = captures.iter().map(|&value| self.value(ops, value)).collect();
        let label = ops.new_dynamic_label();
        self.entries.push((label, PoolEntry::Record(exits, values, name, captures.clone())));
        label
    }

    /// The label of a new entry holding the snapshot of `stores` at
    /// `location`. See Note [Snapshots].
    fn snapshot(&mut self, ops: &mut Assembler, location: Location, stores: impl IntoIterator<Item = Emit>) -> DynamicLabel {
        let stores = stores.into_iter().map(|emit| match emit {
            Emit::Store { slot, reg, unboxed } => (reg, unboxed, slot),
            emit => unreachable!("a flush only stores, not {emit:?}"),
        }).collect();
        let label = ops.new_dynamic_label();
        self.entries.push((label, PoolEntry::Snapshot(Snapshot { location: location.pack(), stores })));
        label
    }
}

/// Whether window ops are copied as stencils at all. Not in a build with debug
/// assertions, whose stencils are unoptimized and too big to copy, nor with
/// `immediate_jit`, which compiles every block, more code than the JIT buffer
/// holds: every window op then runs through its interpreter path, as one the
/// copier rejects does.
const COPIES: bool = !cfg!(debug_assertions) && !cfg!(feature = "immediate_jit");

/// Window-op stencils copied out of this executable, by stencil address, with
/// the `SKIP` each runs at.
#[derive(Default)]
pub struct Stencils {
    image: Option<Result<Image, StencilError>>,
    bodies: HashMap<(usize, usize), (usize, Result<Rc<Body>, StencilError>), FxBuildHasher>,
    /// Each window op the JIT has compiled, by address, and the op it copies
    /// for it (see `effective`); the op kept so its address isn't reused.
    twins: HashMap<usize, (Rc<dyn Window>, Rc<dyn Window>), FxBuildHasher>,
}

impl Stencils {
    /// The op the JIT copies for `op`: its twin, which takes some operands
    /// unboxed, if it has one whose stencils copy, else `op` itself, the same
    /// each time. See Note [Unboxed doubles] in `window_alloc`.
    fn effective(&mut self, op: &Rc<dyn Window>) -> Rc<dyn Window> {
        let key = Rc::as_ptr(op) as *const () as usize;
        if let Some((_, w)) = self.twins.get(&key) {
            return w.clone();
        }
        let w = match op.twin() {
            Some(twin) if !usable_skips(self, &*twin).is_empty() => twin,
            _ => op.clone(),
        };
        self.twins.insert(key, (op.clone(), w.clone()));
        w
    }

    /// The body of `op`'s stencil at `skip`, falling through to its exit
    /// `fall_exit`. See Note [Exit stencils] in `window`.
    fn body(&mut self, op: &dyn Window, skip: usize, fall_exit: usize) -> Result<Rc<Body>, StencilError> {
        if !COPIES {
            return Err(StencilError::Disabled);
        }
        let image = self.image.get_or_insert_with(Image::load).as_ref().map_err(Clone::clone)?;
        self.bodies
            .entry((op.stencil(skip), fall_exit))
            .or_insert_with(|| {
                let body = unsafe { stencil_body(image, op, skip, fall_exit) }
                    .map(Rc::new)
                    .inspect_err(|e| warn!("window op not copied, calling its body instead: {e}"));
                (skip, body)
            })
            .1
            .clone()
    }

    /// Each stencil copied: its address, `SKIP`, and the body splatted.
    #[cfg(feature = "jit_disasm")]
    fn copied(&self) -> impl Iterator<Item = (usize, usize, &Body)> {
        self.bodies.iter().filter_map(|(&(addr, _), (skip, body))| Some((addr, *skip, &**body.as_ref().ok()?)))
    }
}

/// Load the pinned tag's register, r14: on entering a region, and after a
/// frame op. See Note [Pinned tag] in `window`.
fn emit_pin(ops: &mut Assembler) {
    dynasm!(ops
        ; .arch x64
        ; mov r14, QWORD LBoxed::NUMBER_TAG as i64
    );
}

/// The XMM register paired with window register `r`, as `WINDOW_REGS` names
/// its general register: xmm`r`, the stencil ABI's `x{r}`, and for `SCRATCH`
/// xmm15, which no stencil takes. See Note [Unboxed doubles] in `window_alloc`.
fn xmm(r: usize) -> u8 {
    if r == SCRATCH { 15 } else { r as u8 }
}

/// Emit an allocator instruction other than `Emit::Op`. Boxing subtracts the
/// pinned tag and unboxing adds it, as `LBoxed` does (see Note [Pinned tag] in
/// `window`), through r10, never a window register.
fn emit_window_move(ops: &mut Assembler, emit: Emit) {
    let reg = |r: usize| WINDOW_REGS[r];
    match emit {
        Emit::Load { reg: r, slot, unboxed: false } => dynasm!(ops
            ; .arch x64
            ; mov Rq(reg(r)), QWORD [r13 + (slot * 8) as i32]
        ),
        Emit::Load { reg: r, slot, unboxed: true } => dynasm!(ops
            ; .arch x64
            ; mov r10, QWORD [r13 + (slot * 8) as i32]
            ; add r10, r14
            ; vmovq Rx(xmm(r)), r10
        ),
        Emit::Store { slot, reg: r, unboxed: false } => dynasm!(ops
            ; .arch x64
            ; mov QWORD [r13 + (slot * 8) as i32], Rq(reg(r))
        ),
        Emit::Store { slot, reg: r, unboxed: true } => dynasm!(ops
            ; .arch x64
            ; vmovq r10, Rx(xmm(r))
            ; sub r10, r14
            ; mov QWORD [r13 + (slot * 8) as i32], r10
        ),
        Emit::Move { dst, src } => match (dst.unboxed, src.unboxed) {
            (false, false) => dynasm!(ops
                ; .arch x64
                ; mov Rq(reg(dst.reg)), Rq(reg(src.reg))
            ),
            (true, true) => dynasm!(ops
                ; .arch x64
                ; vmovaps Rx(xmm(dst.reg)), Rx(xmm(src.reg))
            ),
            (true, false) => dynasm!(ops
                ; .arch x64
                ; lea r10, [Rq(reg(src.reg)) + r14]
                ; vmovq Rx(xmm(dst.reg)), r10
            ),
            (false, true) => dynasm!(ops
                ; .arch x64
                ; vmovq Rq(reg(dst.reg)), Rx(xmm(src.reg))
                ; sub Rq(reg(dst.reg)), r14
            ),
        },
        // An op is splatted by the caller.
        Emit::Op { .. } => unreachable!(),
    }
}

/// Copy a stencil body into the code: holes are repointed at pool entries with
/// the op's captures, references to the op's continuation at the copy's end, and
/// every other RIP-relative reference at its original target. The body is entered
/// with the stack aligned as just after a call, as it was compiled to expect.
/// Copy `op`, a window op with no operands, into the code at `SKIP` 0, the
/// window empty: its stencil, or else a call of its body. See Note [Frame ops]
/// in `specialize`.
/// The most slots of a callee's frame a call's JIT code nils itself, a store a
/// slot, rather than `PushFrame` with a loop.
const INLINE_NILS: usize = 16;

/// The frame op `$op`, its const params `$pre` then a `Count` of each of
/// `$counts` (see Note [Frame ops] in `specialize`), made from `$args`.
macro_rules! frame_op {
    ($op:ident [$($pre:tt)*] ($($args:expr),*);) => {
        Rc::new(crate::specialize::$op::<$($pre)*>::new($($args,)* &[])) as Rc<dyn Window>
    };
    ($op:ident [$($pre:tt)*] ($($args:expr),*); $count:expr $(, $rest:expr)*) => {
        match crate::specialize::Count::of($count) {
            crate::specialize::Count::Zero => frame_op!($op [$($pre)* { crate::specialize::Count::Zero },] ($($args),*); $($rest),*),
            crate::specialize::Count::One => frame_op!($op [$($pre)* { crate::specialize::Count::One },] ($($args),*); $($rest),*),
            crate::specialize::Count::Two => frame_op!($op [$($pre)* { crate::specialize::Count::Two },] ($($args),*); $($rest),*),
            crate::specialize::Count::Many => frame_op!($op [$($pre)* { crate::specialize::Count::Many },] ($($args),*); $($rest),*),
        }
    };
}

/// A frame op's stencil, copied at `SKIP` 0, or, in a build that copies none, a
/// call running its body. See Note [Frame ops] in `specialize`.
fn emit_frame_op(ops: &mut Assembler, stencils: &mut Stencils, pool: &mut Pool, op: &Rc<dyn Window>) {
    match stencils.body(&**op, 0, 0) {
        Ok(body) => {
            splat(ops, &body, op.name(), &op.captures(), pool, None, Unalign::Target);
        }
        // Debug builds' stencils can keep what optimized ones fold away, but an
        // optimized frame op the copier rejects is a bug to fix.
        Err(e) if !matches!(e, StencilError::Disabled) && !cfg!(debug_assertions) => panic!("{}: {e}", op.name()),
        Err(_) => {
            let (data, vtable) = (Rc::as_ptr(op) as *const dyn Window).to_raw_parts();
            let vtable: *const () = unsafe { core::mem::transmute(vtable) };
            dynasm!(ops
                ; .arch x64
                ; mov rdi, r12 // state
                ; mov rsi, QWORD (data as i64)
                ; mov rdx, QWORD (vtable as i64)
                ; call extern (JitHelper::window_interp as *const () as usize)
            );
        }
    }
    // A frame op's stencil keeps no window, the pinned tag's register included.
    emit_pin(ops);
}

/// How a copy between `sub rsp, 8` and `add rsp, 8` leaves from its middle by
/// the exit it doesn't fall through to. See Note [Stencil alignment] in `window`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Unalign {
    /// Through an `add rsp, 8` after the copy, which its fall-through jumps
    /// over.
    Inline,
    /// At the exit's target, which the caller starts with an `add rsp, 8`.
    Target,
}

/// Copy `body`, its other exit, the one it doesn't fall through to, going to
/// `other`, its cold path's exits too. See Note [Window exits] in `window`.
fn splat(ops: &mut Assembler, body: &Body, name: &'static str, captures: &Captures, pool: &mut Pool, other: Option<DynamicLabel>, unalign: Unalign) {
    enum Site {
        Value(u64),
        Absolute(usize),
        /// Where exit 0 goes.
        Exit0,
        /// The address of where exit 0 goes, in the pool.
        Exit0Address,
        /// The site's record, which its site hole's `lea` gives. See Note
        /// [Cold stencils] in `window`.
        Record,
        /// Where exit 1 goes.
        Exit1,
        /// The way into the cold stencil.
        Cold,
    }
    let fall = ops.new_dynamic_label();
    // The other exit's way from the middle of the copy, out of its alignment
    // first, inline, if the caller doesn't start its target with it.
    let detour = (body.aligned && unalign == Unalign::Inline).then(|| ops.new_dynamic_label());
    let way = detour.or(other);
    // Where each exit goes.
    let exits = [0, 1].map(|exit| match exit == body.fall_exit {
        true => Some(fall),
        false => way,
    });
    // The site's record, if the op has a cold path, and the way into its cold
    // stencil. See Note [Cold stencils] in `window`.
    let has_record = body.cold.is_some() || body.holes.iter().any(|&(_, i)| i == crate::window::SITE_HOLE);
    let record = has_record.then(|| pool.record(ops, exits.map(|exit| exit.unwrap_or(fall)), name, captures));
    let cold_entry = body.cold.map(|stencil| {
        let label = ops.new_dynamic_label();
        pool.stubs.push((label, Stub::ColdEntry { record: record.expect("a record for a cold path"), cold: stencil }));
        label
    });
    let mut sites: SmallVec<[(usize, usize, Site); 8]> = SmallVec::new();
    sites.extend(body.holes.iter().map(|&(r, i)| match i {
        crate::window::SITE_HOLE => (r.end, r.field, Site::Record),
        i => (r.end, r.field, Site::Value(captures[i])),
    }));
    sites.extend(body.relocations().iter().map(|r| (r.end, r.field, Site::Absolute(r.target))));
    sites.extend(body.exit1s.iter().map(|r| (r.end, r.field, Site::Exit1)));
    sites.extend(body.colds.iter().map(|r| (r.end, r.field, Site::Cold)));
    sites.extend(body.nexts.iter().map(|n| match *n {
        NextRef::Direct(r) => (r.end, r.field, Site::Exit0),
        NextRef::Indirect(r) => (r.end, r.field, Site::Exit0Address),
    }));
    sites.sort_by_key(|&(end, ..)| end);

    let rel32 = |kind| dynasmrt::x64::X64Relocation::from_size(kind, RelocationSize::DWord);
    let mut at = 0;
    for (end, field, site) in sites {
        ops.extend(&body.code[at..end]);
        at = end;
        let field_offset = (end - field) as u8;
        match site {
            Site::Absolute(target) => ops.value_relocation(target, field_offset, 0, rel32(RelocationKind::RelToAbs)),
            Site::Exit0 => {
                let to = exits[0].expect("exit 0's way");
                ops.dynamic_relocation(to, 0, field_offset, 0, rel32(RelocationKind::Relative));
            }
            Site::Value(value) => {
                let entry = pool.value(ops, value);
                ops.dynamic_relocation(entry, 0, field_offset, 0, rel32(RelocationKind::Relative));
            }
            Site::Exit0Address => {
                let entry = pool.address(ops, exits[0].expect("exit 0's way"));
                ops.dynamic_relocation(entry, 0, field_offset, 0, rel32(RelocationKind::Relative));
            }
            Site::Record => {
                let record = record.expect("a record for a body with a site hole");
                ops.dynamic_relocation(record, 0, field_offset, 0, rel32(RelocationKind::Relative));
            }
            Site::Exit1 => {
                let to = exits[1].expect("exit 1's way");
                ops.dynamic_relocation(to, 0, field_offset, 0, rel32(RelocationKind::Relative));
            }
            Site::Cold => {
                let entry = cold_entry.expect("a cold path's way in");
                ops.dynamic_relocation(entry, 0, field_offset, 0, rel32(RelocationKind::Relative));
            }
        }
    }
    ops.extend(&body.code[at..body.fall]);
    dynasm!(ops ; .arch x64 ; =>fall);
    ops.extend(&body.code[body.fall..]);
    if let (Some(detour), Some(other)) = (detour, other) {
        let after = ops.new_dynamic_label();
        dynasm!(ops
            ; .arch x64
            ; jmp =>after
            ; =>detour
            ; add rsp, 8
            ; jmp =>other
            ; =>after
        );
    }
}

/// The JIT code buffer's size. `immediate_jit` compiles every block that runs,
/// each as its own region, so it gets twice as much.
const JIT_SIZE: usize = 0x1000 * 16 * if cfg!(feature = "immediate_jit") { 2 } else { 1 };

/// The JIT code buffer's size for this run: `LUNACY_JIT_SIZE` bytes, to measure
/// how much code a program needs past the limit, else `JIT_SIZE`.
fn jit_size() -> usize {
    std::env::var("LUNACY_JIT_SIZE").map_or(JIT_SIZE, |bytes| bytes.parse().expect("LUNACY_JIT_SIZE: a number of bytes"))
}
pub struct JitContext {
    pub memory: std::cell::Cell<dynasmrt::mmap::ExecutableBuffer>,
    pub blocks: HashMap<BlockId, JitBlock, FxBuildHasher>,
    pub pending: BTreeMap<BlockId, Pending>,
    pub stencils: Stencils,
    pub used: usize,
    /// The buffer's size (`jit_size`).
    size: usize,
    /// The shared code of an exit through a snapshot. See Note [Snapshots].
    exit_snapshot: usize,
    pub perf_map: Option<std::cell::RefCell<std::fs::File>>,
    pub window_dump: Option<std::cell::RefCell<std::fs::File>>,
    /// How often each counted piece of allocator code ran (`window_count!`).
    #[cfg(feature = "window_dump")]
    window_counts: std::cell::RefCell<Vec<Box<std::sync::atomic::AtomicU64>>>,
    /// The code committed, and notes on it, disassembled on drop.
    #[cfg(feature = "jit_disasm")]
    pub disasm: crate::disasm::Disasm,
    /// Each thunk compiled into JIT code, by block and offset. See Note
    /// [Thunk patching].
    thunk_sites: HashMap<(BlockId, usize), ThunkSite, FxBuildHasher>,
    /// The thunk sites of the region being compiled, by offset in it.
    region_sites: Vec<(BlockId, usize, usize, Cache)>,
    /// The loop headers of the region being compiled, which start aligned
    /// (`LOOP_ALIGN`) with feature `align_loops`.
    region_headers: std::collections::HashSet<BlockId, FxBuildHasher>,
    /// The line of the function a region being compiled is of, for its
    /// planning's trace events.
    #[cfg(feature = "tracing")]
    traced_line: usize,
    /// The address the region being compiled starts at, which alignment is
    /// relative to.
    region_base: usize,
    /// Thunk sites to patch once their target block has JIT code.
    waiting: HashMap<BlockId, Vec<ThunkSite>, FxBuildHasher>,
    /// The JIT entry of each prototype's all-unknown entry block, by the
    /// prototype's address, once it has one. See `JitHelper::dynamic_call`.
    lua_entries: HashMap<usize, JitExec, FxBuildHasher>,
    /// The `LuaCall` sites of the region being compiled whose callee's version
    /// has no code yet: the version, and the site's and its call's offsets in
    /// the region. See Note [Call linking].
    region_calls: Vec<(BlockId, usize, usize)>,
    /// `LuaCall` sites to link once their callee's version has code, by the
    /// version. See Note [Call linking].
    call_waiting: HashMap<BlockId, Vec<CallSite>, FxBuildHasher>,
    /// The `TailCall` sites of the region being compiled whose callee's version
    /// has no code yet: the version, and the offset of the site's jump in the
    /// region. See Note [Call linking].
    region_tail_calls: Vec<(BlockId, usize)>,
    /// The jumps of `TailCall` sites to link once their callee's version has
    /// code, by the version. See Note [Call linking].
    tail_waiting: HashMap<BlockId, Vec<usize>, FxBuildHasher>,
    /// The frame ops the JIT's code has, which a call of an op's body refers to.
    /// See Note [Frame ops] in `specialize`.
    frame_ops: Vec<Rc<dyn Window>>,
    /// How regions are partitioned into traces (`LUNACY_TRACES`), or `None` to
    /// allocate streaming instead: no plan, each op placing itself in the window
    /// it finds and each block entered with the window of the first jump to it,
    /// for comparison.
    pub trace_policy: Option<Policy>,
}

#[derive(Copy, Clone)]
struct JitPtr(*const u8);

/// A thunk in JIT code: where its nops are, and the window it leaves.
struct ThunkSite {
    at: usize,
    window: Cache,
}

// Note [Call linking]
// ~~~~~~~~~~~~~~~~~~~
// A `LuaCall` whose callee's version has code when the call is compiled calls
// it directly. One whose version has none yet is compiled twice over: first a
// `jmp rel32` to the call through `JitHelper::lua_call` (which takes the
// version's code once it has some, else the generic version's or an exit), then
// the direct call, pushing the frame with `call_lua` and calling the version with
// a `call rel32` whose target is a placeholder. Once a region is compiled from
// the version, and so it has code (`jit_info.entry`), each such site is linked:
// its call's target becomes the version's code, then its jump the five-byte
// nop, so it falls into the direct call from then on. Sites of the region being
// compiled are linked with it, as a recursive call is to its own function.
//
// A `TailCall` whose callee's version has no code yet jumps, with a `jmp rel32`, to an exit
// that has the interpreter run the version; once the version has code, the jump's target
// becomes the version's code.

/// A `LuaCall` site in JIT code waiting for its callee's version to have code:
/// where its jump to the call through `lua_call` is, and its direct call. See
/// Note [Call linking].
struct CallSite {
    site: usize,
    call: usize,
}

/// The window dump ends with how often each counted piece of allocator code
/// ran, and the code is disassembled.
#[cfg(any(feature = "window_dump", feature = "jit_disasm"))]
impl Drop for JitContext {
    fn drop(&mut self) {
        #[cfg(feature = "window_dump")]
        for (id, count) in self.window_counts.borrow().iter().enumerate() {
            window_dump!(self, "count #{id} {}", count.load(std::sync::atomic::Ordering::Relaxed));
        }
        #[cfg(feature = "jit_disasm")]
        {
            let mut symbols: HashMap<usize, String> = self.blocks.iter().map(|(id, block)| (block.ptr.0 as usize, format!("block {}", id.0))).collect();
            let helpers: [(usize, &str); 6] = [
                (JitHelper::check_epoch as *const () as usize, "JitHelper::check_epoch"),
                (JitHelper::check_guard as *const () as usize, "JitHelper::check_guard"),
                (JitHelper::check_hash_guard as *const () as usize, "JitHelper::check_hash_guard"),
                (JitHelper::dynamic_call as *const () as usize, "JitHelper::dynamic_call"),
                (JitHelper::gc_safepoint as *const () as usize, "JitHelper::gc_safepoint"),
                (JitHelper::window_interp as *const () as usize, "JitHelper::window_interp"),
            ];
            symbols.extend(helpers.iter().map(|&(addr, name)| (addr, name.to_string())));
            self.disasm.write("jit_disasm.txt", &symbols);
            crate::disasm::write_stencils("stencil_sizes.txt", self.stencils.copied());
        }
    }
}

/// A compiled block: its code, entered with the window holding `window` (see
/// Note [Window allocation]).
pub struct JitBlock {
    ptr: JitPtr,
    window: Cache,
}

/// A block to compile in the current region: jumps to it go to `label`, with
/// the window holding `window`.
pub struct Pending {
    label: DynamicLabel,
    window: Cache,
}

/// Where planning placed a block's window ops. See Note [Window allocation].
pub struct BlockPlan {
    /// The registers of its entry window.
    entry: Packed,
    /// Those holding theirs unboxed.
    unboxed: u8,
    /// The slots its entry window has dirty, whichever jump into it is
    /// compiled first.
    dirty: Slots,
    /// Whether the trace's edge into it enters more frequent code: its entry
    /// window then has only `dirty` dirty; any other block's also has what the
    /// first jump into it compiled has dirty.
    rises: bool,
    /// Per residual, for a window op with a stencil, its `SKIP` and the placement
    /// planned before it.
    placed: Vec<Option<(u8, Packed)>>,
}

type Plans = HashMap<BlockId, BlockPlan, FxBuildHasher>;

impl BlockPlan {
    /// Its entry window, when `from` is the window of the first jump into it
    /// compiled.
    fn entry_window(&self, from: &Cache) -> Cache {
        let none = Cache::default();
        Cache::entry(self.entry.unpack(), self.unboxed, if self.rises { &none } else { from }, &self.dirty)
    }
}

/// The tag test of a guard of `expected` on the value in register `v`: a
/// match jumps to `pass`, a mismatch falls through. `numeric` if the value is
/// known to be a number. rax, never a window register, is scratch.
///
///   * Integer  : it has all `NUMBER_TAG` bits: at least `NUMBER_TAG`, unsigned.
///   * Double   : some but not all: below `NUMBER_TAG`, and, unless the guard
///     is numeric (the value a number), any set. See Note [Integers] in
///     `specialize`.
///   * Nil/Bool : exact immediate compare (nil = 2, false/true = 6/7).
///   * cell types (Table/Closure/String): the value is a raw pointer (no
///     `NOT_CELL_MASK` bits) whose offset-0 header byte is the kind. We must
///     reject non-cells first so we never dereference a double or an immediate.
fn emit_type_test(ops: &mut Assembler, v: u8, expected: LType, numeric: bool, pass: DynamicLabel) {
    let m = 0; // rax
    match expected {
        LType::Integer => dynasm!(ops
            ; .arch x64
            ; mov Rq(m), QWORD (LBoxed::NUMBER_TAG as i64)
            ; cmp Rq(v), Rq(m)
            ; jae =>pass
        ),
        LType::Double if numeric => dynasm!(ops
            ; .arch x64
            ; mov Rq(m), QWORD (LBoxed::NUMBER_TAG as i64)
            ; cmp Rq(v), Rq(m)
            ; jb =>pass
        ),
        LType::Double => dynasm!(ops
            ; .arch x64
            ; mov Rq(m), QWORD (LBoxed::NUMBER_TAG as i64)
            ; cmp Rq(v), Rq(m)
            ; jae >guard_fail // an integer
            ; test Rq(v), Rq(m)
            ; jnz =>pass
            ; guard_fail:
        ),
        LType::Nil => dynasm!(ops
            ; .arch x64
            ; cmp Rq(v), (LBoxed::VALUE_NIL as i32)
            ; jz =>pass
        ),
        LType::Bool => dynasm!(ops
            ; .arch x64
            ; mov Rq(m), Rq(v)
            ; or Rq(m), 1 // false(6) -> 7, true(7) -> 7
            ; cmp Rq(m), (LBoxed::VALUE_TRUE as i32)
            ; jz =>pass
        ),
        LType::Table => dynasm!(ops
            ; .arch x64
            ; mov Rq(m), QWORD (LBoxed::NOT_CELL_MASK as i64)
            ; test Rq(v), Rq(m)
            ; jnz >guard_fail // not a cell
            ; cmp BYTE [Rq(v)], (LBoxed::KIND_TABLE as i8)
            ; jz =>pass
            ; guard_fail:
        ),
        LType::Closure => dynasm!(ops
            ; .arch x64
            ; mov Rq(m), QWORD (LBoxed::NOT_CELL_MASK as i64)
            ; test Rq(v), Rq(m)
            ; jnz >guard_fail // not a cell
            ; movzx Rd(m), BYTE [Rq(v)]
            ; sub Rd(m), (LBoxed::KIND_LCLOSURE as i32) // LClosure/NClosure, adjacent
            ; cmp Rd(m), 1
            ; jbe =>pass
            ; guard_fail:
        ),
        LType::String => dynasm!(ops
            ; .arch x64
            ; mov Rq(m), QWORD (LBoxed::NOT_CELL_MASK as i64)
            ; test Rq(v), Rq(m)
            ; jnz >guard_fail // not a cell
            ; movzx Rd(m), BYTE [Rq(v)]
            ; sub Rd(m), (LBoxed::KIND_OWNED as i32) // Owned/Interned, adjacent
            ; cmp Rd(m), 1
            ; jbe =>pass
            ; guard_fail:
        ),
        LType::Userdata => dynasm!(ops
            ; .arch x64
            ; mov Rq(m), QWORD (LBoxed::NOT_CELL_MASK as i64)
            ; test Rq(v), Rq(m)
            ; jnz >guard_fail // not a cell
            ; cmp BYTE [Rq(v)], (LBoxed::KIND_USERDATA as i8)
            ; jz =>pass
            ; guard_fail:
        ),
    }
}

/// A type guard tested inline, in the window register caching its slot.
fn inline_guard(res: &Residual) -> bool {
    matches!(res, Residual::Guard {
        expected: LType::Integer | LType::Double | LType::Nil | LType::Bool | LType::Table | LType::Closure | LType::String | LType::Userdata,
        ..
    } | Residual::NumericGuard { .. })
}

/// The `SKIP`s a window op's stencil can be copied at: none where stencils
/// aren't copied (`COPIES`), and the op runs through its interpreter path. A
/// skip is below `WINDOW`, the stencils there are, even for an op with no
/// operands.
fn usable_skips(stencils: &mut Stencils, w: &dyn Window) -> SmallVec<[usize; WINDOW]> {
    (0..=(WINDOW - w.arity()).min(WINDOW - 1)).filter(|&skip| stencils.body(w, skip, 0).is_ok()).collect()
}

/// The alignment of a loop header's code, which a loop's back edge enters on
/// every iteration: where the code falls on the fetch window's and cache line's
/// boundaries otherwise moves with the size of all the code before it.
const LOOP_ALIGN: usize = 32;

/// Multi-byte NOPs, by length (1 to 9 bytes), as the Intel and AMD
/// optimization manuals recommend them.
const NOPS: [&[u8]; 9] = [
    &[0x90],
    &[0x66, 0x90],
    &[0x0f, 0x1f, 0x00],
    &[0x0f, 0x1f, 0x40, 0x00],
    &[0x0f, 0x1f, 0x44, 0x00, 0x00],
    &[0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00],
    &[0x0f, 0x1f, 0x80, 0x00, 0x00, 0x00, 0x00],
    &[0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00],
    &[0x66, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00],
];

/// A cache line, which a branch on `select` doesn't cross (feature
/// `align_selects`): a compare and its conditional jump are fused into one
/// operation, but not across a line.
const CACHE_LINE: usize = 64;

/// The bytes of a `Select`'s test of one target: `cmp rax, imm32; jnz rel32`
/// (dynasm encodes the target's index as an imm32).
const SELECT_TEST: usize = 12;

/// The bytes of a `GuardDynamic`'s test: `cmp qword [r12 + disp32], imm32; jz
/// rel32` (dynasm encodes the 1 as an imm32).
const GUARD_TEST: usize = 18;

/// Pad the code `ops` assembles at `base` with NOPs, which the code before
/// may fall through, to a multiple of `align`: the bytes padded.
fn pad(ops: &mut Assembler, base: usize, align: usize) -> usize {
    let padding = (align - (base + ops.offset().0) % align) % align;
    let mut left = padding;
    while left > 0 {
        let nop = NOPS[left.min(NOPS.len()) - 1];
        ops.extend(nop);
        left -= nop.len();
    }
    padding
}

/// How many of a block's residuals its code runs: up to its first jump or thunk no guard before
/// it can skip. See Note [Contraction] in `specialize`.
fn runs_to(residuals: &[Residual]) -> usize {
    // Whether the residual before can skip this one: a guard's side exit.
    let mut guarded = false;
    for (off, res) in residuals.iter().enumerate() {
        if matches!(res, Residual::Jump(_) | Residual::Thunk(_)) && !guarded {
            return off + 1;
        }
        guarded = matches!(res, Residual::Guard { .. } | Residual::NumericGuard { .. } | Residual::NativeGuard { .. }
            | Residual::LuaGuard { .. } | Residual::GuardWitness { .. } | Residual::EpochCheck { .. } | Residual::HashGuard { .. }
            | Residual::GuardDynamic(_) | Residual::ReturnedFrom(_));
    }
    residuals.len()
}

/// The blocks a residual jumps to.
fn jump_targets(res: &Residual) -> SmallVec<[BlockId; 2]> {
    match res {
        Residual::Jump(target) => smallvec::smallvec![*target],
        Residual::Select(targets) => targets.iter().map(|target| target.1).collect(),
        Residual::Branch { hot, cold } => smallvec::smallvec![*hot, *cold],
        _ => SmallVec::new(),
    }
}

impl JitContext {
    pub fn new() -> Self {
        let size = jit_size();
        let near = Self::find_near(size);
        assert!(near != core::ptr::null_mut());
        let mut memory = dynasmrt::mmap::MutableBuffer::new_with_hint(size, near).unwrap();
        debug!("allocated JIT memory @ {:?}", memory.as_ptr());
        // Set the JIT memory to the max size initially, so that we don't need to
        // mprotect back to mutable just to reserve
        memory.set_len(size);
        let mut perf_map = None;
        #[cfg(feature = "perf")]
        {
            perf_map = {
                let pid = std::process::id();
                let path = format!("/tmp/perf-{}.map", pid);
                std::fs::File::create(path).ok().map(|f| std::cell::RefCell::new(f))
            };
        }
        let mut window_dump = None;
        #[cfg(feature = "window_dump")]
        {
            window_dump = std::fs::File::create("window_dump.txt").ok().map(std::cell::RefCell::new);
        }
        let mut jctx = Self {
            memory: Cell::new(memory.make_exec().unwrap()),
            blocks: HashMap::default(),
            pending: BTreeMap::new(),
            thunk_sites: HashMap::default(),
            region_sites: Vec::new(),
            region_headers: Default::default(),
            #[cfg(feature = "tracing")]
            traced_line: 0,
            region_base: 0,
            waiting: HashMap::default(),
            lua_entries: HashMap::default(),
            region_calls: Vec::new(),
            call_waiting: HashMap::default(),
            region_tail_calls: Vec::new(),
            tail_waiting: HashMap::default(),
            frame_ops: Vec::new(),
            stencils: Stencils::default(),
            // `LUNACY_JIT_PADDING` bytes are left unused at the buffer's start,
            // to time the same code at other places in its cache lines.
            used: std::env::var("LUNACY_JIT_PADDING").map_or(0, |bytes| bytes.parse().expect("LUNACY_JIT_PADDING: a number of bytes")),
            size,
            exit_snapshot: 0,
            perf_map,
            window_dump,
            #[cfg(feature = "window_dump")]
            window_counts: Default::default(),
            #[cfg(feature = "jit_disasm")]
            disasm: Default::default(),
            trace_policy: match std::env::var("LUNACY_TRACES").as_deref() {
                Ok("streaming") => None,
                _ => Some(Policy::from_env()),
            },
        };
        jctx.emit_snapshot_code();
        jctx
    }

    /// Commit `flush_snapshot` and `exit_snapshot`, with rax a snapshot's
    /// address. See Note [Snapshots].
    fn emit_snapshot_code(&mut self) {
        let base = self.end();
        let mut ops = Assembler::new(base.0 as usize);
        let flush = ops.offset();
        jit_note!(self, ops, "flush_snapshot");
        // Window register `i` at `[rsp + i * 8]`, its XMM half at `[rsp +
        // (WINDOW + i) * 8]`.
        dynasm!(ops ; .arch x64 ; sub rsp, (WINDOW * 8) as i32);
        for r in 0..WINDOW {
            dynasm!(ops ; .arch x64 ; vmovq QWORD [rsp + (r * 8) as i32], Rx(xmm(r)));
        }
        for &reg in WINDOW_REGS[..WINDOW].iter().rev() {
            dynasm!(ops ; .arch x64 ; push Rq(reg));
        }
        dynasm!(ops
            ; .arch x64
            ; mov ecx, DWORD [rax + 8]
            ; lea rdx, [rax + 12]
            ; test ecx, ecx
            ; jz >done
            ; store:
            ; movzx esi, WORD [rdx]
            ; movzx edi, WORD [rdx + 2]
            ; mov r8, QWORD [rsp + rdi * 8]
            // An XMM half's value, boxed.
            ; cmp edi, WINDOW as i32
            ; jb >boxed
            ; sub r8, r14
            ; boxed:
            ; mov QWORD [r13 + rsi * 8], r8
            ; add rdx, 4
            ; dec ecx
            ; jnz <store
            ; done:
            // The offset of the `PackedLocation`.
            ; movzx ecx, WORD [rax + 4]
            ; mov WORD r12 => RunState.current_off, cx
        );
        for &reg in &WINDOW_REGS[..WINDOW] {
            dynasm!(ops ; .arch x64 ; pop Rq(reg));
        }
        dynasm!(ops ; .arch x64 ; add rsp, (WINDOW * 8) as i32 ; ret);
        let exit = ops.offset();
        jit_note!(self, ops, "exit_snapshot");
        // A trap at the snapshot's block and `current_off`, what a region
        // returns for one: see `Specializer::run`.
        dynasm!(ops
            ; .arch x64
            ; call extern base.0 as usize + flush.0
            ; mov BYTE r12 => RunState.trap, 1
            ; mov eax, DWORD [rax]
            ; mov rcx, QWORD ((-4i32 as u64) << 32) as i64
            ; or rax, rcx
            ; pop r13
            ; pop rbx
            ; pop rbp
            ; ret
        );
        let buf = ops.finalize().unwrap();
        self.reserve(buf.len());
        let code = self.commit(base, &buf).expect("committed snapshot code") as usize;
        #[cfg(feature = "jit_disasm")]
        self.disasm.committed(code, buf.len(), "snapshot code".to_string());
        self.add_to_perf_map(code, buf.len(), "jit_snapshot_code");
        self.exit_snapshot = code + exit.0;
    }

    pub fn add_to_perf_map(&self, addr: usize, size: usize, name: &str) {
        #[cfg(feature = "perf")]
        if let Some(ref map) = self.perf_map {
            let mut map = map.borrow_mut();
            writeln!(map, "{:x} {:x} {}", addr, size, name).ok();
        }
    }

    fn find_near(size: usize) -> *mut core::ffi::c_void {
        let target = JitHelper::check_guard as *mut u8 as usize;
        let MAX_DIST = 2isize.pow(31);
        let maps = rsprocmaps::from_path("/proc/self/maps").unwrap();
        // Our goal is to find an available place in memory such that our entire `size` buffer is
        // within 2GB of the target.
        // This means that we can
        // 1) allocate memory before it, with a start <2GB away, and a `size` hole
        // 2) allocate memory after it, with a start <2GB-`size` away, and a `size` hole
        // Really this needs to have the target be a *range* and require a buffer that is within
        // distance of both the start and end, and then we should compute the start and end based
        // off all of our closure call targets...but it isn't likely to matter, so we don't.
        let res = maps.map_windows(|[first, second]| {
            let (Ok(first), Ok(second)) = (first, second) else { return None };
            // Case 1
            if (target as isize - first.address_range.end as isize).abs() < MAX_DIST && (second.address_range.begin - first.address_range.end) as usize >= size {
                debug!("Found near JIT location @ {:#x}", first.address_range.end);
                return Some(first.address_range.end as *mut core::ffi::c_void);
            }
            None
        }).flatten().next();
        res.unwrap_or(core::ptr::null_mut())
    }

    fn end(&self) -> JitPtr {
        let mut buf = self.memory.take();
        let ptr = JitPtr(unsafe { buf.as_ptr().add(self.used).cast() });
        self.memory.set(buf);
        ptr
    }

    // Reserve memory in the JIT buffer
    fn reserve(&mut self, len: usize) {
        assert!(self.used + len < self.size, "JIT code past the end of its buffer");
        self.used += len;
    }

    // Commit contents 
    fn commit(&mut self, ptr: JitPtr, contents: &[u8]) -> Option<*mut u8> {
        let mut mutable = self.memory.take().make_mut().unwrap();
        #[cfg(debug_assertions)]
        {
            assert!(ptr.0 >= mutable.as_mut_ptr());
            assert!(ptr.0 <= unsafe { mutable.as_mut_ptr().add(self.used) });
            assert!(unsafe { ptr.0.add(contents.len()) } <= unsafe { mutable.as_mut_ptr().add(self.used) });
        }
        let ptr = unsafe { mutable.as_mut_ptr().offset(ptr.0.offset_from(mutable.as_mut_ptr())) };
        unsafe { core::slice::from_raw_parts_mut(ptr, contents.len()).copy_from_slice(contents) };
        self.memory.set(mutable.make_exec().unwrap());
        Some(ptr)
    }

    /// Overwrite committed code at `at` with `bytes`.
    fn patch(&mut self, at: usize, bytes: &[u8]) {
        let mut mutable = self.memory.take().make_mut().unwrap();
        let start = mutable.as_mut_ptr() as usize;
        assert!(at >= start && at + bytes.len() <= start + self.used, "patching outside committed code");
        unsafe { core::slice::from_raw_parts_mut(at as *mut u8, bytes.len()).copy_from_slice(bytes) };
        self.memory.set(mutable.make_exec().unwrap());
    }
}

impl<'src, 'intern> Specializer<'src, 'intern> {
    pub fn jit_compile(&mut self, id: BlockId, owner: &mut Owner) {
        #[cfg(feature = "tracing")]
        crate::tracing::begin("jit", "compile", &[("block_id", id.0.into())]);
        debug!("JIT compiling block {:?}", id);
        window_dump!(self.jctx, "== region entered at block {}", id.0);
        let base = self.jctx.end();
        self.jctx.region_base = base.0 as usize;
        let mut ops = dynasmrt::VecAssembler::<dynasmrt::x64::X64Relocation>::new(base.0 as usize);
        let entry = ops.offset();
        jit_note!(self.jctx, ops, "region entry: prologue");

        // SystemV ABI is RDI, RSI, RDX, RCX, R8, R9
        // JitExec (rust-preserve-none): R12=state, R13=base_ptr

        dynasm!(ops
            ; .arch x64
            ; push rbp
            ; mov rbp, rsp
            ; push rbx
            ; push r13 // save initial base_ptr
        );
        emit_pin(&mut ops);
        // TODO: Pin state.vals.as_ptr() to a register, which will let us remove a lot of the
        // JitHelper function calls.

        let mut compiled_offsets = Vec::new();
        let mut pool = Pool::default();
        let mut plans = Plans::default();
        // We may have already JIT this block, if it was jumped to by another block
        // first. In that case we just have to jump to it.
        let mut successor = None;
        if let Some(block) = self.jctx.blocks.get(&id) {
            // Load the window the block is entered with.
            let loads = WindowAlloc::default().transfer(&block.window);
            jit_note!(self.jctx, ops, "load the window block {} is entered with, and jump to it", id.0);
            let counted = window_count!(self.jctx, &mut ops, loads);
            window_dump!(self.jctx, "block {} compiled already, entered with {}: {}{counted}", id.0, block.window, emits_line(&loads));
            for emit in loads {
                emit_window_move(&mut ops, emit);
            }
            self.load_returned(&mut ops, id);
            dynasm!(ops
            ; jmp extern block.ptr.0 as usize
            );
        } else {
            // Load the window the block is entered with, clean from the stack
            // (empty, streaming).
            // A thunk waiting to be linked into the block is the one whose path
            // got it hot: it's entered with that thunk's window. See Note [Thunk
            // patching].
            let linked = self.jctx.waiting.get(&id).and_then(|sites| sites.last()).map(|site| site.window.clone());
            let window = match self.jctx.trace_policy {
                Some(policy) => {
                    #[cfg(feature = "tracing")]
                    {
                        self.jctx.traced_line = unsafe { (*self.clos.ro(owner).prototype).line_defined } as usize;
                    }
                    plans = self.plan_region(id, policy, linked.as_ref());
                    plans[&id].entry_window(linked.as_ref().unwrap_or(&Cache::default()))
                }
                None => linked.clone().unwrap_or_default(),
            };
            let loads = WindowAlloc::default().transfer(&window);
            jit_note!(self.jctx, ops, "load the entry window");
            let counted = window_count!(self.jctx, &mut ops, loads);
            window_dump!(self.jctx, "region entry block {} loads {}{counted}", id.0, emits_line(&loads));
            for emit in loads {
                emit_window_move(&mut ops, emit);
            }
            self.load_returned(&mut ops, id);
            // A loop header starts aligned. The entry's code is reserved as a
            // whole below, padding and all.
            #[cfg(feature = "align_loops")]
            if self.jctx.region_headers.contains(&id) {
                jit_note!(self.jctx, ops, "loop header padding, to {LOOP_ALIGN} bytes");
                pad(&mut ops, base.0 as usize, LOOP_ALIGN);
            }
            // We need to skip over the uncommitted prologue
            let new_block = JitPtr(unsafe { base.0.add(ops.offset().0) });
            self.jctx.blocks.insert(id, JitBlock { ptr: new_block, window });
            let start_off = ops.offset().0;
            let (_block, entry_succ) = self.jit_block(id, &mut ops, &mut pool, owner, &plans);
            successor = entry_succ;
            compiled_offsets.push((id, start_off, ops.offset().0));
        }


        // Reserve the full length of our compiled function
        let end = ops.offset();
        self.jctx.reserve(end.0);

        // Now we need to go through and also compile all of the pending labels for other blocks.
        loop {
            // Try to use the successor label first, if it exists
            // Else pop the next pending
            // If there are none remaining, we're done.
            let successor_pair = successor.and_then(|succ| self.jctx.pending.remove(&succ).map(|pending| (succ, pending)));
            let Some((pending_block, pending)) = successor_pair.or_else(|| self.jctx.pending.pop_first()) else { break };
            debug!("pending block {:?} {:?}", pending_block.0, pending.label);
            // A loop header starts aligned: its padding reserved first, so the
            // block's pointer is past it.
            #[cfg(feature = "align_loops")]
            if self.jctx.region_headers.contains(&pending_block) {
                jit_note!(self.jctx, ops, "loop header padding, to {LOOP_ALIGN} bytes");
                let padding = pad(&mut ops, base.0 as usize, LOOP_ALIGN);
                self.jctx.reserve(padding);
            }
            let pending_ptr = self.jctx.end();
            let pending_start = ops.offset();
            self.jctx.blocks.insert(pending_block, JitBlock { ptr: pending_ptr, window: pending.window });
            dynasm!(ops
                ; =>pending.label
            );
            let (_block, next_succ) = self.jit_block(pending_block, &mut ops, &mut pool, owner, &plans);
            successor = next_succ;
            compiled_offsets.push((pending_block, pending_start.0, ops.offset().0));
            self.jctx.reserve(ops.offset().0 - pending_start.0);
        }

        let stubs = ops.offset();
        for (label, stub) in std::mem::take(&mut pool.stubs) {
            dynasm!(ops ; .arch x64 ; =>label);
            match stub {
                Stub::ColdEntry { record, cold } => {
                    jit_note!(self.jctx, ops, "into a cold stencil");
                    dynasm!(ops
                        ; .arch x64
                        ; lea rax, [=>record]
                        ; mov QWORD r12 => RunState.cold_site, rax
                        ; jmp extern cold
                    );
                }
                Stub::Select { aligned, exit, join } => {
                    jit_note!(self.jctx, ops, "exit {exit}, selected");
                    if aligned {
                        dynasm!(ops ; .arch x64 ; add rsp, 8);
                    }
                    dynasm!(ops
                        ; .arch x64
                        ; mov QWORD r12 => RunState.select, exit as i32
                        ; jmp =>join
                    );
                }
                Stub::Way { aligned, moves, to, count } => {
                    jit_note!(self.jctx, ops, "an exit's way");
                    if aligned {
                        dynasm!(ops ; .arch x64 ; add rsp, 8);
                    }
                    if let Some(at) = count {
                        emit_count(&mut ops, at);
                    }
                    for emit in moves {
                        emit_window_move(&mut ops, emit);
                    }
                    match to {
                        JumpTo::Code(code) => dynasm!(ops ; .arch x64 ; jmp extern code),
                        JumpTo::Label(label) => dynasm!(ops ; .arch x64 ; jmp =>label),
                    }
                }
            }
        }
        self.jctx.reserve(ops.offset().0 - stubs.0);

        let epilogue = ops.offset();
        jit_note!(self.jctx, ops, "exit_jit: epilogue");
        dynasm!(ops
            ; .arch x64
            ; ->exit_jit:
            ; pop r13
            ; pop rbx
            ; pop rbp
            ; ret
        );
        self.jctx.reserve(ops.offset().0 - epilogue.0);

        let pool_start = ops.offset();
        ops.align(8, 0xcc);
        jit_note!(self.jctx, ops, "{}", crate::disasm::POOL);
        // Records last: their displacements are to value entries, which are
        // then placed.
        let (records, entries): (Vec<_>, Vec<_>) = pool.entries.into_iter().partition(|(_, entry)| matches!(entry, PoolEntry::Record(..)));
        for (label, entry) in entries.into_iter().chain(records) {
            let bytes = match entry {
                PoolEntry::Value(value) => value.to_le_bytes().to_vec(),
                PoolEntry::Address(target) => {
                    let offset = ops.labels().resolve_dynamic(target).expect("pool entry for a placed label");
                    ((base.0 as usize + offset.0) as u64).to_le_bytes().to_vec()
                }
                PoolEntry::Snapshot(snapshot) => snapshot.bytes(),
                PoolEntry::Record(exits, values, _name, _captures) => {
                    jit_note!(self.jctx, ops, "site record of {_name}: captures {:x?}", _captures.as_slice());
                    let mut bytes = Vec::new();
                    for exit in exits {
                        let offset = ops.labels().resolve_dynamic(exit).expect("a record for a placed site");
                        bytes.extend(((base.0 as usize + offset.0) as u64).to_le_bytes());
                    }
                    // Placed here, as every entry is 8 bytes aligned.
                    let here = ops.offset().0 as isize;
                    for value in values {
                        let at = ops.labels().resolve_dynamic(value).expect("a record's value placed before it").0 as isize;
                        bytes.extend(i32::try_from(at - here).expect("a pool within i32 of its records").to_le_bytes());
                    }
                    bytes.resize(bytes.len().next_multiple_of(8), 0);
                    bytes
                }
            };
            dynasm!(ops ; =>label);
            ops.extend(&bytes);
        }
        self.jctx.reserve(ops.offset().0 - pool_start.0);

        debug!("drained pending");
        let buf = ops.finalize().unwrap();
        let Some(slab) = self.jctx.commit(base, buf.as_slice()) else { panic!() };
        let entrypoint: JitExec = unsafe { core::mem::transmute(slab.add(entry.0)) };
        for (block, off, at, window) in std::mem::take(&mut self.jctx.region_sites) {
            self.jctx.thunk_sites.insert((block, off), ThunkSite { at: slab as usize + at, window });
        }
        // Thunk sites waiting for a block compiled here jump to it now.
        let ready: Vec<BlockId> = self.jctx.waiting.keys().filter(|target| self.jctx.blocks.contains_key(target)).copied().collect();
        for target in ready {
            for site in self.jctx.waiting.remove(&target).unwrap() {
                self.patch_thunk(site, target);
            }
        }

        let (source, line) = {
            let proto = self.clos.ro(owner).prototype;
            let source = unsafe { String::from_utf8_lossy((*proto).source.data).to_string().replace("\0", "") };
            let line = unsafe { (*proto).line_defined };
            (source, line)
        };
        #[cfg(feature = "jit_disasm")]
        self.jctx.disasm.committed(slab as usize, buf.len(), format!("region entered at block {}, function {source}:{line}", id.0));

        #[cfg(feature = "perf")]
        {
            for (bid, start, end) in compiled_offsets {
                self.jctx.add_to_perf_map(
                    unsafe { slab.add(start) } as usize,
                    end - start,
                    &format!("jit_block_{} {}:{}", bid.0, source, line)
                );
            }
            self.jctx.perf_map.as_mut().map(|mut map| map.get_mut().sync_all());
        }

        self.blocks[id.0 as usize].jit_info.entry = Some(entrypoint);
        #[cfg(feature = "tracing")]
        crate::tracing::end("jit", "compile", &[("source", source.as_str().into()), ("line", (line as u64).into())]);
        // Calls waiting for this block to have code call it now, this region's
        // too. See Note [Call linking].
        for (block, site, call) in std::mem::take(&mut self.jctx.region_calls) {
            let site = CallSite { site: slab as usize + site, call: slab as usize + call };
            self.jctx.call_waiting.entry(block).or_default().push(site);
        }
        for site in self.jctx.call_waiting.remove(&id).unwrap_or_default() {
            self.link_call(site, entrypoint);
        }
        for (block, jump) in std::mem::take(&mut self.jctx.region_tail_calls) {
            self.jctx.tail_waiting.entry(block).or_default().push(slab as usize + jump);
        }
        for jump in self.jctx.tail_waiting.remove(&id).unwrap_or_default() {
            self.link_tail_call(jump, entrypoint);
        }
    }

    /// Make the `TailCall` site whose jump is at `jump` jump to `code`. See
    /// Note [Call linking].
    fn link_tail_call(&mut self, jump: usize, code: JitExec) {
        assert!(unsafe { *(jump as *const u8) == 0xe9 }, "a tail call site's jump");
        let rel = i32::try_from(code as isize - (jump as isize + 5)).expect("a version's code within rel32 of a tail call to it");
        let mut bytes = [0xe9, 0, 0, 0, 0];
        bytes[1..].copy_from_slice(&rel.to_le_bytes());
        self.jctx.patch(jump, &bytes);
    }

    /// Where a region is entered at `id` from the interpreter, and `id` starts
    /// with a continuation guard, the call's return value it compares, from
    /// `RunState::returned`. See Note [Call continuations] in `specialize`.
    fn load_returned(&self, ops: &mut Assembler, id: BlockId) {
        if let Some(Residual::ReturnedFrom(_)) = self.blocks[id.0].instructions.first() {
            jit_note!(self.jctx, ops, "the return the entry's continuation guard compares");
            dynasm!(ops
                ; .arch x64
                ; mov rax, QWORD r12 => RunState.returned
            );
        }
    }

    /// Make the call site `site` call `code` directly. See Note [Call linking].
    fn link_call(&mut self, site: CallSite, code: JitExec) {
        // Emitted as a `jmp rel32` and a `call rel32`, which the patches replace.
        assert!(unsafe { *(site.site as *const u8) == 0xe9 && *(site.call as *const u8) == 0xe8 }, "a call site's jump and call");
        let rel = i32::try_from(code as isize - (site.call as isize + 5)).expect("a version's code within rel32 of a call to it");
        let mut call = [0xe8, 0, 0, 0, 0];
        call[1..].copy_from_slice(&rel.to_le_bytes());
        // The call's target first, so the direct call is complete before the
        // jump stops skipping it.
        self.jctx.patch(site.call, &call);
        self.jctx.patch(site.site, &NOP5);
    }

    /// The JIT entry of `lclos`'s all-unknown entry block, if it has one.
    fn lua_entry(&mut self, owner: &Owner, lclos: &Tc<LClosure<'src, 'intern>>) -> Option<JitExec> {
        let proto = lclos.ro(owner).prototype;
        if let Some(&entry) = self.jctx.lua_entries.get(&(proto as usize)) {
            return Some(entry);
        }
        let next_stack = unsafe { (*proto).max_stack.into() };
        let ctx = Rc::new(Context::new(next_stack));
        let block = *self.versions.get(&proto)?.get(&(SubPc::new(0), ctx))?;
        let entry = self.blocks[block.0].jit_info.entry?;
        self.jctx.lua_entries.insert(proto as usize, entry);
        Some(entry)
    }

    /// The thunk at `off` in `block` is now a jump to `target`: patch its JIT
    /// code, if any, now or once `target` has some. See Note [Thunk patching].
    pub fn link_thunk(&mut self, block: BlockId, off: usize, target: BlockId) {
        // Whether the site was compiled, not whether it ran: a thunk that never
        // ran is linked when it first runs and is forced, to a target compiled
        // by then or not.
        let Some(site) = self.jctx.thunk_sites.remove(&(block, off)) else { return };
        if self.jctx.blocks.contains_key(&target) {
            self.patch_thunk(site, target);
        } else {
            self.jctx.waiting.entry(target).or_default().push(site);
        }
    }

    /// Make the thunk site `site` jump into `target`'s JIT code, through its
    /// compensation code.
    fn patch_thunk(&mut self, site: ThunkSite, target: BlockId) {
        let stub = self.thunk_stub(&site.window, target);
        let rel = i32::try_from(stub as isize - (site.at as isize + NOP5.len() as isize)).expect("a thunk stub within rel32 of its site");
        let mut jmp = [0xe9, 0, 0, 0, 0];
        jmp[1..].copy_from_slice(&rel.to_le_bytes());
        self.jctx.patch(site.at, &jmp);
    }

    /// The compensation code a patched thunk site jumps to: the transfer from
    /// the thunk's `window` to `target`'s entry window, then a jump into it.
    fn thunk_stub(&mut self, window: &Cache, target: BlockId) -> usize {
        let block = &self.jctx.blocks[&target];
        let (ptr, entry) = (block.ptr, block.window.clone());
        let base = self.jctx.end();
        let mut ops = dynasmrt::VecAssembler::<dynasmrt::x64::X64Relocation>::new(base.0 as usize);
        let emits = WindowAlloc::entering(window.clone()).transfer(&entry);
        jit_note!(self.jctx, ops, "from the thunk's window {} to block {}'s {}", window, target.0, entry);
        let counted = window_count!(self.jctx, &mut ops, emits);
        window_dump!(self.jctx, "thunk linked from {} into block {} entered with {}: {}{counted}", window, target.0, entry, emits_line(&emits));
        for emit in emits {
            emit_window_move(&mut ops, emit);
        }
        dynasm!(ops
            ; .arch x64
            ; jmp extern ptr.0 as usize
        );
        let buf = ops.finalize().unwrap();
        self.jctx.reserve(buf.len());
        let stub = self.jctx.commit(base, &buf).expect("a committed thunk stub") as usize;
        #[cfg(feature = "jit_disasm")]
        self.jctx.disasm.committed(stub, buf.len(), format!("thunk stub into block {}", target.0));
        stub
    }

    /// Plan the window allocation of the region compiled from `entry`: the blocks
    /// reachable from it not compiled yet, partitioned into traces by the JIT's
    /// policy, each trace planned by one pass. See Note [Trace register
    /// allocation].
    /// With `entered`, the entry's trace starts from that window.
    fn plan_region(&mut self, entry: BlockId, policy: Policy, entered: Option<&Cache>) -> Plans {
        let mut ids = vec![entry];
        let mut index: HashMap<BlockId, usize, FxBuildHasher> = HashMap::default();
        index.insert(entry, 0);
        let mut next = 0;
        while let Some(&block) = ids.get(next) {
            next += 1;
            let residuals = &self.blocks[block.0].instructions;
            for target in residuals[..runs_to(residuals)].iter().flat_map(jump_targets) {
                if !self.jctx.blocks.contains_key(&target) && !index.contains_key(&target) {
                    index.insert(target, ids.len());
                    ids.push(target);
                }
            }
        }
        // The op the JIT copies for each window op, and its usable `SKIP`s; one
        // with none is called, a flush.
        let stencils = &mut self.jctx.stencils;
        let windows: Vec<Vec<Option<Rc<dyn Window>>>> = ids
            .iter()
            .map(|block| {
                self.blocks[block.0]
                    .instructions
                    .iter()
                    .map(|res| match res {
                        Residual::ExecWindow(w) | Residual::GuardDynamic(w) => Some(stencils.effective(w)),
                        _ => None,
                    })
                    .collect()
            })
            .collect();
        let skips: Vec<Vec<SmallVec<[usize; WINDOW]>>> = windows
            .iter()
            .map(|block| block.iter().map(|w| w.as_ref().map_or_else(SmallVec::new, |w| usable_skips(stencils, &**w))).collect())
            .collect();
        let slots_of = |placement: &Placement| {
            let mut slots = Slots::default();
            placement.iter().flatten().for_each(|&slot| slots.insert(slot));
            slots
        };
        let region = Region::new(
            ids.iter()
                .zip(&skips)
                .map(|(block, skips)| {
                    let mut events = Vec::new();
                    let residuals = &self.blocks[block.0].instructions;
                    for (off, res) in residuals[..runs_to(residuals)].iter().enumerate() {
                        match res {
                            Residual::ExecWindow(w) | Residual::GuardDynamic(w) if !skips[off].is_empty() => {
                                let operands = w.operands().iter().zip(w.accesses());
                                events.extend(operands.clone().filter(|(_, a)| a.reads()).map(|(&slot, _)| Event::Read(slot)));
                                events.extend(operands.filter(|(_, a)| a.writes()).map(|(&slot, _)| Event::Write(slot)));
                            }
                            Residual::Guard { idx, .. } | Residual::NumericGuard { idx, .. } if inline_guard(res) => events.push(Event::Read(*idx)),
                            // Reads its field through the witness, no slot.
                            Residual::GuardWitness { .. } => {}
                            Residual::Jump(_) | Residual::Select(_) | Residual::Branch { .. } => {
                                for target in jump_targets(res) {
                                    events.push(match index.get(&target) {
                                        Some(&i) => Event::Edge(i),
                                        None => Event::Exit(slots_of(self.jctx.blocks[&target].window.regs())),
                                    });
                                }
                            }
                            // An exit to the interpreter, which reads the stack.
                            Residual::Thunk(_) => {}
                            _ => events.push(Event::Flush),
                        }
                    }
                    TraceBlock {
                        events,
                        hotness: self.blocks[block.0].jit_info.hotness.get(),
                        id: block.0,
                        pc: self.blocks[block.0].pc,
                        // A block whose countdown hasn't moved never ran. Every
                        // block starts hot with `immediate_jit`, so none counts.
                        ran: cfg!(feature = "immediate_jit") || self.blocks[block.0].jit_info.hotness.get() < INITIAL_HOTNESS,
                    }
                })
                .collect(),
        );
        let live_in = region.liveness();
        let loops = region.loops();
        self.jctx.region_headers = region.loop_headers().map(|header| ids[header]).collect();
        let traces = region.traces(policy);
        window_dump!(self.jctx, "traces {}", traces.iter().map(|trace| trace.iter().map(|&b| ids[b].0.to_string()).collect::<Vec<_>>().join(" ")).collect::<Vec<_>>().join(" | "));
        for (b, live) in live_in.iter().enumerate() {
            window_dump!(self.jctx, "live into block {}: {:?}", ids[b].0, live.iter().collect::<Vec<_>>());
        }
        // The window each trace's head starts from, and the block it comes
        // from: the region's entry, the window of the thunk linked into it,
        // from outside the region; another head, the window the hottest edge
        // into it from a trace planned earlier leaves. See Note [Trace
        // allocation].
        let mut hints: HashMap<BlockId, (usize, Cache, Option<usize>), FxBuildHasher> = HashMap::default();
        if let Some(window) = entered {
            hints.insert(entry, (0, window.clone(), None));
        }
        let mut plans = Plans::default();
        for trace in &traces {
            let head = ids[trace[0]];
            let (hint, from) = hints.get(&head).map(|(_, window, from)| (window.clone(), *from)).unwrap_or_default();
            window_dump!(self.jctx, "trace from block {} starts from {}", head.0, hint);
            let (planned, exits) = self.plan_trace(trace, &ids, &windows, &skips, &index, &live_in, &loops, &plans, &hint, from);
            for (from, target, window) in exits {
                let hotness = self.blocks[from.0].jit_info.hotness.get();
                if hints.get(&target).is_none_or(|&(hottest, ..)| hotness < hottest) {
                    hints.insert(target, (hotness, window, Some(index[&from])));
                }
            }
            plans.extend(planned);
        }
        plans
    }

    /// Plan one trace's window ops from `hint`, the window of an edge from the
    /// region's block `from` or from outside it (see Note [Trace allocation]):
    /// its blocks' residuals as steps, each block continuing into the next,
    /// the last into its hottest target unless it jumps back into the trace.
    /// Returns its blocks' plans and, per edge leaving the trace, its source,
    /// its target and the window it leaves.
    fn plan_trace(
        &self,
        trace: &[usize],
        ids: &[BlockId],
        windows: &[Vec<Option<Rc<dyn Window>>>],
        skips: &[Vec<SmallVec<[usize; WINDOW]>>],
        index: &HashMap<BlockId, usize, FxBuildHasher>,
        live_in: &[Slots],
        loops: &Loops,
        plans: &Plans,
        hint: &Cache,
        from: Option<usize>,
    ) -> (Vec<(BlockId, BlockPlan)>, Vec<(BlockId, BlockId, Cache)>) {
        let slots_of = |placement: &Placement| {
            let mut slots = Slots::default();
            placement.iter().flatten().for_each(|&slot| slots.insert(slot));
            slots
        };
        // What a block the trace leaves into reads first: its entry window's
        // slots, or those live into it; none for a side exit that never ran.
        let reads = |target: BlockId, hot: bool| match self.jctx.blocks.get(&target) {
            Some(done) => slots_of(done.window.regs()),
            None if !hot && !cfg!(feature = "immediate_jit") && self.blocks[target.0].jit_info.hotness.get() >= INITIAL_HOTNESS => Slots::default(),
            None => plans.get(&target).map_or(live_in[index[&target]], |plan| slots_of(&plan.entry.unpack())),
        };
        let position = |target: BlockId| trace.iter().position(|&t| ids[t] == target);
        let mut steps = Vec::new();
        let mut starts = Vec::new();
        let mut step_of = Vec::new();
        let mut leaving = Vec::new();
        for (pos, &b) in trace.iter().enumerate() {
            let block = &self.blocks[ids[b].0];
            let next = trace.get(pos + 1).map(|&n| ids[n]);
            // The jump the trace goes on to `next` through: the block's last to it.
            let ran = &block.instructions[..runs_to(&block.instructions)];
            let flow = next.and_then(|next| ran.iter().rposition(|res| jump_targets(res).contains(&next)));
            let targets = || ran.iter().flat_map(jump_targets);
            let back = targets().any(|target| position(target).is_some_and(|at| at <= pos));
            let continues = if next.is_none() && !back {
                targets().min_by_key(|target| (self.blocks[target.0].jit_info.hotness.get(), target.0))
            } else {
                None
            };
            // Whether the edge into the block enters more frequent code.
            let rise = loops.entered(if pos == 0 { from } else { Some(trace[pos - 1]) }, b);
            starts.push(steps.len());
            steps.push(Step::Start(rise.map(|(mut reads, writes)| {
                reads.intersect(&live_in[b]);
                Rise { reads, writes }
            })));
            let mut of = vec![None; block.instructions.len()];
            for (off, res) in block.instructions[..runs_to(&block.instructions)].iter().enumerate() {
                match res {
                    Residual::ExecWindow(_) | Residual::GuardDynamic(_) if !skips[b][off].is_empty() => {
                        of[off] = Some(steps.len());
                        steps.push(Step::Op(&**windows[b][off].as_ref().expect("a window op"), skips[b][off].clone()));
                    }
                    Residual::Guard { idx, .. } | Residual::NumericGuard { idx, .. } if inline_guard(res) => steps.push(Step::Read(*idx)),
                    Residual::GuardWitness { .. } => {}
                    Residual::Jump(_) | Residual::Select(_) | Residual::Branch { .. } => {
                        for target in jump_targets(res) {
                            if Some(off) == flow && Some(target) == next {
                                continue;
                            }
                            match position(target).filter(|&at| at <= pos) {
                                Some(at) => steps.push(Step::Back(starts[at])),
                                None => {
                                    let hot = Some(target) == continues;
                                    leaving.push((steps.len(), ids[b], target));
                                    steps.push(Step::Exit { hot, reads: reads(target, hot) });
                                }
                            }
                        }
                    }
                    Residual::Thunk(_) => {}
                    _ => steps.push(Step::Flush),
                }
            }
            step_of.push(of);
        }
        // The trace's steps' blocks and residuals, for the planner's trace events.
        #[cfg(feature = "tracing")]
        let traced = {
            static TRACES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
            let id = TRACES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let line = self.jctx.traced_line;
            for (pos, &b) in trace.iter().enumerate() {
                let (block, pc) = (ids[b].0, self.blocks[ids[b].0].pc);
                let ops = step_of[pos].iter().enumerate().filter_map(|(off, step)| Some((off, (*step)?)));
                for (off, step) in std::iter::once((usize::MAX, starts[pos])).chain(ops) {
                    crate::tracing::instant("alloc", "step", &[
                        ("trace", id.into()),
                        ("step", step.into()),
                        ("line", line.into()),
                        ("block", block.into()),
                        ("pc", pc.into()),
                        ("off", off.into()),
                    ]);
                }
            }
            id
        };
        #[cfg(not(feature = "tracing"))]
        let traced = 0;
        let plan = plan_trace(&steps, ALLOCATED, hint, traced);
        let exits = leaving.into_iter().filter_map(|(step, from, target)| Some((from, target, plan.exits[step].clone()?))).collect();
        let placed = |of: &[Option<usize>]| of.iter().map(|step| step.map(|step| (plan.skips[step] as u8, Packed::pack(&plan.windows[step])))).collect();
        let planned = trace
            .iter()
            .enumerate()
            .map(|(pos, &b)| {
                let start = starts[pos];
                let rises = !plan.trivial && matches!(steps[start], Step::Start(Some(_)));
                (ids[b], BlockPlan { entry: Packed::pack(&plan.windows[start]), unboxed: plan.unboxed[start], dirty: plan.dirty[start], rises, placed: placed(&step_of[pos]) })
            })
            .collect();
        (planned, exits)
    }

    /// JIT compile one block, returning the JIT code offset and optionally the next block to
    /// compile.
    pub fn jit_block(&mut self, id: BlockId, ops: &mut Assembler, pool: &mut Pool, owner: &mut Owner, plans: &Plans) -> (AssemblyOffset, Option<BlockId>) {
        // The address `JitHelper::dynamic_call` gets: this code only runs while
        // `self`, which owns it, is alive and in place.
        let spec = &*self as *const Self as i64;
        // We try to bias the default exit as the next block to compile. This is only a suggestion,
        // and doesn't affect correctness; `GUARD; JMP failure; RET;` for example may say that
        // `failure` is the "next block" despite not quite being correct.
        let mut successor = None;
        // Where the op just copied has the exit it doesn't fall through to go,
        // whether its copy is aligned, and which it falls through to, for the
        // `Select` or `Branch` after it to lay its ways: that residual then tests
        // no `select`. See Note [Window exits] in `window`.
        let mut fused: Option<(DynamicLabel, bool, usize)> = None;
        let entry = ops.offset();
        let x = self.jctx.memory.get_mut().as_ptr();
        let block = &self.blocks[id.0];
        let insts: Vec<_> = block.instructions.iter().map(|_| ops.new_dynamic_label()).collect();
        let mut alloc = WindowAlloc::entering(self.jctx.blocks[&id].window.clone());
        window_dump!(self.jctx, "block {} hotness {} pc {} entered with {}", id.0, block.jit_info.hotness.get(), block.pc, alloc.cache());
        jit_note!(self.jctx, ops, "block {} (pc {}, hotness {}) entered with {}", id.0, block.pc, block.jit_info.hotness.get(), alloc.cache());

        // Jump to `target`, or fall through to it if `skip`, transferring the
        // window to the one it is entered with: its planned entry window, dirty where the
        // first jump to it compiled delivers it dirty.
        // With `defer`, its moves and target, for code laid out elsewhere, in
        // place of emitting it.
        let mut emit_jump = |ops: &mut Assembler, alloc: &WindowAlloc, target: &BlockId, skip: bool, defer: bool| -> Option<(SmallVec<[Emit; 16]>, JumpTo, Option<i64>)> {
            if let Some(target_block) = self.jctx.blocks.get(target) {
                // We already JIT compiled the block, and can jump to it directly.
                let transfer = alloc.transfer(&target_block.window);
                let (counted, count) = if defer { window_deferred!(self.jctx, transfer) } else { (window_count!(self.jctx, ops, transfer), None) };
                window_dump!(self.jctx, "      to block {} (compiled, entered with {}): {}{counted}", target.0, target_block.window, emits_line(&transfer));
                if defer {
                    return Some((transfer, JumpTo::Code(target_block.ptr.0 as usize), count));
                }
                for emit in transfer {
                    emit_window_move(ops, emit);
                }
                if !skip {
                    dynasm!(ops
                        ; jmp extern target_block.ptr.0 as usize
                    );
                }
            } else {
                // The block could already be pending from another block in this assembler
                // set. Use it if it already exists, otherwise create a new label for our
                // relocation.
                let pending = self.jctx.pending.entry(*target).or_insert_with(|| Pending {
                    label: ops.new_dynamic_label(),
                    window: match plans.get(target) {
                        Some(plan) => plan.entry_window(alloc.cache()),
                        // Streaming: entered with the window of the first jump to it.
                        None => alloc.cache().clone(),
                    },
                });
                let transfer = alloc.transfer(&pending.window);
                let (counted, count) = if defer { window_deferred!(self.jctx, transfer) } else { (window_count!(self.jctx, ops, transfer), None) };
                window_dump!(self.jctx, "      to block {} (entered with {}): {}{counted}", target.0, pending.window, emits_line(&transfer));
                if defer {
                    return Some((transfer, JumpTo::Label(pending.label), count));
                }
                for emit in transfer {
                    emit_window_move(ops, emit);
                }
                if !skip {
                    dynasm!(ops
                        ; jmp =>pending.label
                    );
                }
            }
            None
        };

        let emit_bailout = |ops: &mut Assembler, off| {
            if off == 0 {
                // If we're trying to bailout from the first instruction, we
                // need to record it as a JIT exit so that we don't try to call
                // this same function again immediately in a loop.
                dynasm!(ops
                    ; .arch x64
                    ; mov WORD r12 => RunState.current_off, (off as i16)
                    ; mov rax, QWORD (((-1i32 as u64) << 32 | (id.0 as u64)) as i64)
                    ; mov BYTE r12 => RunState.trap, 1
                    ; jmp ->exit_jit
                );
            } else {
                // Fallback to interpreter for other residuals
                dynasm!(ops
                    ; .arch x64
                    ; mov rax, QWORD (Location(BlockId(id.0), off).pack().bits() as i64)
                    ; mov BYTE r12 => RunState.trap, 1
                    ; jmp ->exit_jit
                );
            }
        };

        // Charge `cost` residuals of gas at residual `off`, exiting if it runs out
        // (after `stores`, which bring the stack up to date with the window).
        #[cfg(feature = "gas")]
        let emit_gas_check = |ops: &mut Assembler, off: usize, cost: usize, stores: &[Emit]| {
            dynasm!(ops
                ; sub QWORD r12 => RunState.gas, cost as i32
                ; mov WORD r12 => RunState.current_off, (off as i16)
                ; ja >have_gas
            );
            for &emit in stores {
                emit_window_move(ops, emit);
            }
            dynasm!(ops
                ; mov rax, QWORD (((-1i32 as u64) << 32 | (id.0 as u64)) as i64)
                ; mov BYTE r12 => RunState.trap, 1
                ; jmp ->exit_jit
                ; have_gas:
            );
        };

        // The window carries values across window residuals, the inline type
        // guards between them, and jumps to other blocks (see Note [Window
        // allocation]). A thunk stores the dirty registers before it exits; any
        // other residual flushes the window after its label, since a guard's
        // success edge may jump there with the window live. A guard's failure
        // edge is an ordinary fall through (docs/jit-register-cache.md, "Flush
        // points"). Every edge into a label carries the same window: a jump or
        // thunk leaves the window as it was, for the guard success edge that
        // reaches the residual after it, and a window residual following another
        // gets no label, so a jump to one fails to assemble. A `GuardDynamic` is a
        // window residual whose op is the guard's test.
        // A call to whatever slot `a` holds, through `JitHelper::dynamic_call`: a
        // native has run, a Lua function's JIT entry is called with its frame
        // pushed, and anything else bails out for the interpreter to call.
        // `helper` is `dynamic_call`, or `lua_call` for a `LuaCall`, which takes the call's
        // version if it has code by then. A native's results are in place, so it
        // continues past the `Arrive` after the call (Note [Returns]).
        // `natives`: whether the callee may be a native, after which the code skips the call's
        // `Arrive` (a `LuaCall`'s is a Lua function's, which returns to the residual after it).
        let emit_dynamic_call = |ops: &mut Assembler, off: usize, a: u16, b: u16, c: u16, helper: usize, natives: bool| {
            let ret = Location(BlockId(id.0), off + 1).pack().bits() as u64;
            dynasm!(ops
                ; .arch x64
                ; mov rdi, QWORD spec
                ; mov rsi, r12 // state
                ; mov rdx, QWORD (ret as i64)
                ; mov ecx, a as i32
                ; mov r8d, b as i32
                ; mov r9d, c as i32
                ; call extern (helper)
            );
            if natives {
                assert!(matches!(block.instructions.get(off + 1), Some(Residual::Arrive { .. })), "a call not followed by its `Arrive`");
                let past_arrive = insts[off + 2];
                dynasm!(ops
                    ; .arch x64
                    // A native's error exits as an exec's trap does. See Note [Errors] in
                    // `specialize`.
                    ; cmp BYTE r12 => RunState.trap, 0
                    ; jz >no_trap
                    ; mov rax, QWORD (((-1i32 as u64) << 32 | (id.0 as u64)) as i64)
                    ; jmp ->exit_jit
                    ; no_trap:
                    ; cmp rax, 1
                    // One, we just fully called a native function and we need to skip the Arrive
                    // operation immediately after this.
                    ; je =>past_arrive
                );
            }
            dynasm!(ops
                ; .arch x64
                ; test rax, rax
                // Zero, so need to bailout so the interpreter can do the call instead.
                ; jz >bail
                // Function pointer to more JIT code, and the helper pushed a frame for us.
                // Do the call.
                ; mov r10, rax
                // The callee's base: vals.stack_ptr + base * sizeof(LBoxed)
                ; lea rcx, r12 => RunState.vals
                ; mov rax, QWORD rcx => ValueStack<'src, 'intern>.stack_ptr
                ; mov rcx, QWORD r12 => RunState.base
                ; lea r13, [rax + rcx * 8]
                ; call r10
                ; mov r13, QWORD [rsp - 0]
                ; cmp BYTE r12 => RunState.trap, 0
                ; jnz ->exit_jit
                ; jmp >done
                ; bail:
            );
            emit_bailout(ops, off);
            dynasm!(ops
                ; .arch x64
                ; done:
            );
        };
        let window = |r: &Residual| matches!(r, Residual::ExecWindow(_) | Residual::GuardDynamic(_));
        let jump = |r: &Residual| matches!(r, Residual::Jump(_) | Residual::Select(_) | Residual::Branch { .. });
        let end = runs_to(&block.instructions);
        for (off, res) in block.instructions[..end].iter().enumerate() {
            debug!("JIT operation {res:?}");
            window_dump!(self.jctx, "  {off:3} {res}");
            jit_note!(self.jctx, ops, "  {off:3} {res}");
            let prev = off.checked_sub(1).map(|p| &block.instructions[p]);
            let keeps_window = window(res) || inline_guard(res) || jump(res) || matches!(res, Residual::Thunk(_) | Residual::GuardWitness { .. });
            if window(res) && prev.is_some_and(|p| window(p)) {
                // Inside a run of window residuals, charged for with its first.
            } else {
                let label = insts[off];
                dynasm!(ops
                    ; => label
                );
                if !keeps_window && !alloc.is_empty() {
                    let stores = alloc.flush();
                    let counted = window_count!(self.jctx, ops, stores);
                    window_dump!(self.jctx, "      flush: {}{counted}", emits_line(&stores));
                    for emit in stores {
                        emit_window_move(ops, emit);
                    }
                }
                #[cfg(feature = "gas")]
                emit_gas_check(ops, off, block.instructions[off..].iter().take_while(|r| window(r)).count().max(1), &alloc.stores());
            }
            loop { match res {
                Residual::Guard { idx, expected } | Residual::NumericGuard { idx, expected } if inline_guard(res) => {
                    let numeric = matches!(res, Residual::NumericGuard { .. });
                    // NuN-boxed type check of the value in `STACK[idx]`: in the window
                    // register caching it, or else loaded from its stack home. A
                    // *match* jumps to the success continuation at `off + 2`, a
                    // *mismatch* falls through to the failure edge at `off + 1`,
                    // both with the window live. `v` holds the value: its window
                    // register, or else r10.
                    let v = match alloc.register_of(*idx) {
                        // Unboxed, boxed into r10 for the test, the window as it was.
                        Some(reg) if alloc.cache().loc(reg).unboxed => {
                            window_dump!(self.jctx, "      tests r10 <- x{reg} boxed");
                            dynasm!(ops
                                ; .arch x64
                                ; vmovq r10, Rx(xmm(reg))
                                ; sub r10, r14
                            );
                            10 // r10
                        }
                        Some(reg) => {
                            window_dump!(self.jctx, "      tests w{reg}");
                            WINDOW_REGS[reg]
                        }
                        None => {
                            // Counted as the load it is, into r10.
                            let counted = window_count!(self.jctx, ops, [()]);
                            window_dump!(self.jctx, "      tests r10 <- [{idx}]{counted}");
                            dynasm!(ops
                                ; .arch x64
                                ; mov r10, QWORD r13 => LBoxed<'src, 'intern>[*idx as i32]
                            );
                            10 // r10
                        }
                    };
                    emit_type_test(ops, v, *expected, numeric, insts[off + 2]);
                },
                Residual::GuardWitness { href, expected } => {
                    // A `Guard` of hash key `href`'s field: its value, through the
                    // frame's witness of it (Note [Hash witnesses] in `vm`), into r10,
                    // then the same test, with the window live.
                    window_dump!(self.jctx, "      tests r10 <- witness {}", href.0);
                    let witnesses = (core::mem::offset_of!(RunState<'static, 'static>, hash_witnesses) + Witnesses::DATA) as i32;
                    let base = core::mem::offset_of!(RunState<'static, 'static>, witness_base) as i32;
                    let size = core::mem::size_of::<HashWitness>() as i32;
                    let value = (href.0 as i32) * size + core::mem::offset_of!(HashWitness, value) as i32;
                    dynasm!(ops
                        ; .arch x64
                        ; mov r10, QWORD [r12 + witnesses]
                        ; imul rax, QWORD [r12 + base], size
                        ; mov r10, QWORD [r10 + rax + value]
                        ; mov r10, QWORD [r10]
                    );
                    emit_type_test(ops, 10, *expected, false, insts[off + 2]);
                },
                Residual::Guard { idx, expected, .. } => {
                    // A type with no inline test: ask `check_guard`. The window was
                    // flushed, since the call clobbers it.
                    let expected_u8 = *expected as u8;
                    dynasm!(ops
                        ; .arch x64
                        ; mov rdi, r12 // state
                        ; mov rsi, WORD (*idx as i32) // idx
                        ; mov rdx, WORD (expected_u8 as i32) // expected
                        ; call extern (JitHelper::check_guard as *const () as usize)
                        ; test al, 1 // a returned bool is bit 0: the rest of al may not be zero
                        ; jnz =>insts[off + 2]
                        // Fail: fallthrough to next (off + 1)
                    );
                },
                Residual::NativeGuard { idx, ptr } => {
                    // The value is a raw (leaked) `NClosureCell` pointer; load its
                    // `native` fn pointer and compare to the specialized target.
                    dynasm!(ops
                        ; .arch x64
                        ; mov rax, QWORD r13 => LBoxed<'src, 'intern>[*idx as i32]
                        ; mov rcx, QWORD (*ptr as i64)
                        ; cmp rcx, QWORD rax => NClosureCell.native
                        ; jz =>insts[off + 2]
                        // Fail: fallthrough to next (off + 1)
                    );
                },
                Residual::LuaGuard { idx, ptr } => {
                    // The value is a raw `Gc` (GcInner base); step to the inner
                    // `LClosure` (`GcInner.val`, valid since TCell is transparent)
                    // and compare its `prototype` to the specialized identity.
                    dynasm!(ops
                        ; .arch x64
                        ; mov rax, QWORD r13 => LBoxed<'src, 'intern>[*idx as i32]
                        ; lea rax, rax => GcInner<TLCell<TlcOwner, LClosure<'src, 'intern>>>.val
                        ; mov rcx, QWORD (*ptr as i64)
                        ; cmp rcx, QWORD rax => LClosure<'src, 'intern>.prototype
                        ; jz =>insts[off + 2]
                        // Fail: fallthrough to next (off + 1)
                    );
                },
                Residual::EpochCheck { tab, href, place } => {
                    let href_u8 = href.0;
                    dynasm!(ops
                        ; .arch x64
                        ; mov rdi, r12 // state
                        ; mov rsi, QWORD (*tab as i64)
                        ; mov rdx, WORD (href_u8 as i32)
                        ; mov rcx, WORD (place.bits() as i32)
                        ; call extern (JitHelper::check_epoch as *const () as usize)
                        ; test al, 1 // a returned bool is bit 0: the rest of al may not be zero
                        ; jnz =>insts[off + 2]
                        // Fail: fallthrough to next (off + 1)
                    );
                },
                Residual::HashGuard { tab, href, key, expected } => {
                    let href_u8 = href.0;
                    let expected_u8 = *expected as u8;
                    dynasm!(ops
                        ; .arch x64
                        ; mov rdi, r12 // state
                        ; mov rsi, QWORD (*tab as i64)
                        ; mov rdx, WORD (href_u8 as i32)
                        ; mov rcx, WORD (expected_u8 as i32)
                        ; mov r8, QWORD (*key as i64)
                        ; call extern (JitHelper::check_hash_guard as *const () as usize)
                        ; test al, 1 // a returned bool is bit 0: the rest of al may not be zero
                        ; jnz =>insts[off + 2]
                        // Fail: fallthrough to next (off + 1)
                    );
                },
                Residual::Exec(f) => {
                    let (this_obj, this_vtable, this_call) = get_ptr_from_closure(f.body.as_ref());
                    debug!("JIT memory @ {:?}, operation @ {:#x}, desired {:?}", x, this_call, &mut JitHelper::check_guard as &mut _ as *mut _ as *mut core::ffi::c_void);
                    dynasm!(ops
                        ; .arch x64
                        ; mov rsi, QWORD FORGED_OWNER // owner
                        ; mov rdx, r12 // state
                        ; mov rdi, QWORD (this_obj as i64)
                        ; mov rax, QWORD (this_vtable as i64)
                        // Lua wants to see PC+1, and also we want to resume to PC+1 if we trap.
                        ; mov WORD r12 => RunState.current_off, ((off + 1) as i16)
                        ; call extern (this_call)
                        //// Check for trap
                        ; mov al, BYTE r12 => RunState.trap
                        ; test al, al
                        ; jz >no_trap
                        //// Trap 4 so specializer can handle it
                        ; mov rax, QWORD (((-1i32 as u64) << 32 | (id.0 as u64)) as i64)
                        ; jmp ->exit_jit
                        ; no_trap:
                    );
                },
                Residual::LuaCall { entry, a, b, c, stack, vararg } => {
                    // The callee's version's code, if the call has found the version
                    // and it has some; a version with none yet is linked when it has
                    // some (Note [Call linking]); else the call goes as one to a
                    // function the JIT doesn't know. See Note [Call sites].
                    // `PushFrame` pushes the frame of a function that isn't vararg
                    // only: a call of a vararg one goes as one to a function the JIT
                    // doesn't know. See Note [Vararg frames] in `vm`.
                    let version = match entry {
                        CallEntry::Block(block) if !*vararg => Some(*block),
                        _ => None,
                    };
                    let code = version.and_then(|block| self.blocks[block.0].jit_info.entry);
                    match version {
                        None => emit_dynamic_call(ops, off, *a, *b, *c, JitHelper::lua_call as *const () as usize, false),
                        Some(version) => {
                            let site = ops.offset().0;
                            if code.is_none() {
                                dynasm!(ops
                                    ; .arch x64
                                    ; jmp >lua_call
                                );
                            }
                            // The frame, pushed by `PushFrame` returning here, with what its
                            // entry would hold kept on the native stack: put back when it
                            // returns, or written as its entry if it bails out. See Note
                            // [Frame ops] in `specialize`.
                            // The callee's frame past a fixed count of arguments is
                            // nilled here, a store a slot, but for a big one, which
                            // `PushFrame` nils, as it does past a count up to the top.
                            let packed_ret = Location(BlockId(id.0), off + 1).pack();
                            let hold = crate::specialize::Count::hold;
                            let (held_a, held_b) = (hold(*a), hold(*b));
                            let nils = (*b != 0).then(|| (*b as usize - 1)..*stack as usize).filter(|nils| nils.len() <= INLINE_NILS);
                            let push = match nils {
                                Some(_) => frame_op!(PushFrame [false,] (held_a, held_b, *stack); *a, *b),
                                None => frame_op!(PushFrame [true,] (held_a, held_b, *stack); *a, *b),
                            };
                            jit_note!(self.jctx, ops, "        keep the caller's frame");
                            dynasm!(ops
                                ; .arch x64
                                ; push QWORD r12 => RunState.clos
                                ; push QWORD r12 => RunState.base
                                ; push QWORD r12 => RunState.witness_base
                                ; push QWORD r12 => RunState.witness_top
                            );
                            jit_note!(self.jctx, ops, "        PushFrame");
                            emit_frame_op(ops, &mut self.jctx.stencils, pool, &push);
                            self.jctx.frame_ops.push(push);
                            jit_note!(self.jctx, ops, "        enter the callee");
                            dynasm!(ops
                                ; .arch x64
                                // Reload r13 = callee base ptr = vals.stack_ptr + base*sizeof(LBoxed)
                                ; lea rcx, r12 => RunState.vals
                                ; mov rax, QWORD rcx => ValueStack<'src, 'intern>.stack_ptr
                                ; mov rcx, QWORD r12 => RunState.base
                                ; lea r13, [rax + rcx * 8]
                            );
                            // Nil in rax once, free past the callee's base: each store of it, of
                            // a slot near the base, is 4 bytes.
                            let nils = nils.unwrap_or_default();
                            if !nils.is_empty() {
                                let nil = i32::try_from(LBoxed::NIL.bits()).expect("nil is a sign-extended imm32");
                                dynasm!(ops ; .arch x64 ; mov eax, nil);
                            }
                            for slot in nils {
                                match i8::try_from(slot * 8) {
                                    Ok(disp) => dynasm!(ops ; .arch x64 ; mov QWORD [BYTE r13 + disp], rax),
                                    Err(_) => dynasm!(ops ; .arch x64 ; mov QWORD [DWORD r13 + (slot * 8) as i32], rax),
                                }
                            }
                            // state is already in r12
                            match code {
                                Some(code) => dynasm!(ops
                                    ; .arch x64
                                    ; call extern (code as usize)
                                ),
                                None => {
                                    // A placeholder target, linked to the version's code.
                                    self.jctx.region_calls.push((version, site, ops.offset().0));
                                    dynasm!(ops
                                        ; .arch x64
                                        ; call >lua_call
                                    );
                                },
                            }
                            jit_note!(self.jctx, ops, "        put back the caller's frame, or unwind");
                            dynasm!(ops
                                ; .arch x64
                                // A bailout in the callee: its frame's entry is written from
                                // what was kept, and the bailout goes on to this code's caller.
                                ; cmp BYTE r12 => RunState.trap, 0
                                ; jz >call_returned
                                ; mov rdi, r12
                                ; mov rsi, rsp
                                ; mov rdx, QWORD (packed_ret.bits() as i64)
                                ; mov rcx, rax
                                ; call extern (JitHelper::unwind_frame as *const () as usize)
                                ; add rsp, 32
                                ; jmp ->exit_jit
                                ; call_returned:
                                ; pop QWORD r12 => RunState.witness_top
                                ; pop QWORD r12 => RunState.witness_base
                                ; pop QWORD r12 => RunState.base
                                ; pop QWORD r12 => RunState.clos
                                ; mov r13, QWORD [rsp - 0]
                            );
                            if code.is_none() {
                                dynasm!(ops
                                    ; .arch x64
                                    ; jmp >lua_call_done
                                    ; lua_call:
                                );
                                emit_dynamic_call(ops, off, *a, *b, *c, JitHelper::lua_call as *const () as usize, false);
                                dynasm!(ops
                                    ; .arch x64
                                    ; lua_call_done:
                                );
                            }
                        },
                    }
                },
                Residual::TailCall { entry: CallEntry::Block(version), a, b, closes, vararg, effects, callee_effects } => {
                    // The frame, replaced by `TailFrame`; then this code's own native
                    // frame is left, as the region's epilogue leaves it, and the callee's
                    // version's code entered with a jump, so its return is to what called
                    // this code. See Note [Tail calls] in `specialize`.
                    let hold = |count: u16| crate::specialize::Count::hold(count) as u64;
                    let (ab, effects, callee) = (hold(*a) | hold(*b) << 16, *effects as u64, *callee_effects as u64);
                    let tail = match (*closes, *vararg) {
                        (false, false) => frame_op!(TailFrame [false, false,] (ab, effects, callee); *a, *b),
                        (false, true) => frame_op!(TailFrame [false, true,] (ab, effects, callee); *a, *b),
                        (true, false) => frame_op!(TailFrame [true, false,] (ab, effects, callee); *a, *b),
                        (true, true) => frame_op!(TailFrame [true, true,] (ab, effects, callee); *a, *b),
                    };
                    jit_note!(self.jctx, ops, "        TailFrame");
                    emit_frame_op(ops, &mut self.jctx.stencils, pool, &tail);
                    self.jctx.frame_ops.push(tail);
                    jit_note!(self.jctx, ops, "        leave this code's frame, and enter the callee");
                    dynasm!(ops
                        ; .arch x64
                        ; pop r13
                        ; pop rbx
                        ; pop rbp
                        // The callee's base: vals.stack_ptr + base * sizeof(LBoxed)
                        ; lea rcx, r12 => RunState.vals
                        ; mov rax, QWORD rcx => ValueStack<'src, 'intern>.stack_ptr
                        ; mov rcx, QWORD r12 => RunState.base
                        ; lea r13, [rax + rcx * 8]
                    );
                    match self.blocks[version.0].jit_info.entry {
                        Some(code) => dynasm!(ops
                            ; .arch x64
                            ; jmp extern (code as usize)
                        ),
                        None => {
                            // Linked to the version's code once it has some. See Note [Call
                            // linking].
                            self.jctx.region_tail_calls.push((*version, ops.offset().0));
                            dynasm!(ops
                                ; .arch x64
                                ; jmp >no_code
                                ; no_code:
                                // The interpreter runs the version's first residual, as a
                                // bailout from a block's first one does.
                                ; mov WORD r12 => RunState.current_off, 0
                                ; mov rax, QWORD (((-1i32 as u64) << 32 | (version.0 as u64)) as i64)
                                ; mov BYTE r12 => RunState.trap, 1
                                ; ret
                            );
                        },
                    }
                },
                Residual::NativeCall { nf, a, b, c } if *c == 0 => {
                    // Taking every result, which may be more than the call's slots
                    // (`unpack`): `call_native` makes room for them.
                    // An error it raises exits as an exec's trap does. See Note [Errors]
                    // in `specialize`.
                    dynasm!(ops
                        ; .arch x64
                        ; mov rdi, r12 // state
                        ; mov rsi, QWORD (*nf as usize as i64)
                        ; mov edx, *a as i32
                        ; mov ecx, *b as i32
                        ; mov WORD r12 => RunState.current_off, ((off + 1) as i16)
                        ; call extern (JitHelper::native_call as *const () as usize)
                        ; cmp BYTE r12 => RunState.trap, 0
                        ; jz >no_trap
                        ; mov rax, QWORD (((-1i32 as u64) << 32 | (id.0 as u64)) as i64)
                        ; jmp ->exit_jit
                        ; no_trap:
                    );
                },
                Residual::NativeCall { nf, a, b, c } => {
                    // Native signature `fn(seq, args, returns, owner)` with ZST seq/owner,
                    // so the two `&[LBoxed]` slice views arrive as (rdi=args ptr, rsi=args
                    // len, rdx=returns ptr, rcx=returns len); r13 is `&vals[base]`. `a/b/c`
                    // are compile-time constants, so specialize the lengths per site: a
                    // fixed count when b/c are non-zero, else up to `RunState.top` for the
                    // "to top-of-stack" (0) shape. Then call the native directly.
                    let (a, b, c) = (*a as i32, *b as i32, *c as i32);
                    if b == 0 {
                        dynasm!(ops
                            ; .arch x64
                            ; mov rax, QWORD r12 => RunState.top
                            ; sub rax, QWORD r12 => RunState.base
                            ; sub rax, (a + 1)
                            ; mov rsi, rax
                        );
                    } else {
                        dynasm!(ops ; .arch x64 ; mov rsi, (b - 1));
                    }
                    // Every result goes in the slots the function and its
                    // arguments took: `b` of them, or up to the top.
                    if c == 0 && b == 0 {
                        dynasm!(ops
                            ; .arch x64
                            ; mov rax, QWORD r12 => RunState.top
                            ; sub rax, QWORD r12 => RunState.base
                            ; sub rax, a
                            ; mov rcx, rax
                        );
                    } else if c == 0 {
                        dynasm!(ops ; .arch x64 ; mov rcx, b);
                    } else if c == 1 {
                        dynasm!(ops ; .arch x64 ; xor ecx, ecx);
                    } else {
                        dynasm!(ops ; .arch x64 ; mov rcx, (c - 1));
                    }
                    dynasm!(ops
                        ; .arch x64
                        ; lea rdi, [r13 + ((a + 1) * 8)] // args ptr = &vals[base + a + 1]
                        ; lea rdx, [r13 + (a * 8)]       // returns ptr = &vals[base + a]
                        ; call extern (*nf as usize)     // direct, statically-known target
                    );
                    // It returns a `Result<usize, LBoxed>`: in al bit 0 whether it's an
                    // error, and in rdx the count or the error. An error exits as an
                    // exec's trap does. See Note [Errors] in `specialize`.
                    dynasm!(ops
                        ; .arch x64
                        ; test al, 1
                        ; jz >native_ok
                        ; mov rdi, r12
                        ; mov rsi, rdx
                        ; mov WORD r12 => RunState.current_off, ((off + 1) as i16)
                        ; call extern (JitHelper::raise as *const () as usize)
                        ; mov rax, QWORD (((-1i32 as u64) << 32 | (id.0 as u64)) as i64)
                        ; jmp ->exit_jit
                        ; native_ok:
                        ; mov rax, rdx
                    );
                    // Taking every result, the caller reads up to the top: the
                    // native returns how many it wrote, within the slots it got.
                    if c == 0 {
                        if b == 0 {
                            dynasm!(ops
                                ; .arch x64
                                ; mov rcx, QWORD r12 => RunState.top
                                ; sub rcx, QWORD r12 => RunState.base
                                ; sub rcx, a
                            );
                        } else {
                            dynasm!(ops ; .arch x64 ; mov rcx, b);
                        }
                        dynasm!(ops
                            ; .arch x64
                            ; cmp rax, rcx
                            ; cmova rax, rcx
                            ; add rax, QWORD r12 => RunState.base
                            ; add rax, a
                            ; mov QWORD r12 => RunState.top, rax
                        );
                    }
                    // Wanting `c - 1`, the ones it didn't write are nil.
                    let nil = i32::try_from(LBoxed::NIL.bits()).expect("nil is a sign-extended imm32");
                    for i in 0..(c - 1).max(0) {
                        dynasm!(ops
                            ; .arch x64
                            ; cmp rax, i
                            ; ja >written
                            ; mov QWORD [r13 + ((a + i) * 8)], nil
                            ; written:
                        );
                    }
                },
                Residual::Call { a, b, c } => emit_dynamic_call(ops, off, *a, *b, *c, JitHelper::dynamic_call as *const () as usize, true),
                Residual::ReturnedFrom(from) => {
                    // The call's return value, still in rax, from the `Ret` expected: its
                    // continuation goes on to `off + 2`, else falls through to the thunk for the
                    // next return. See Note [Call continuations] in `specialize`.
                    let from = pool.value(ops, *from);
                    dynasm!(ops
                        ; .arch x64
                        ; cmp rax, QWORD [=>from]
                        ; je =>insts[off + 2]
                    );
                },
                Residual::Arrived { a, c, returned } => {
                    // The results, as `Arrive` takes them, of a return of `returned`: the
                    // missing ones nil. See Note [Call continuations] in `specialize`.
                    if *c != 0 {
                        let (at, end) = (*a as usize, *a as usize + *c as usize - 1);
                        let nil = i32::try_from(LBoxed::NIL.bits()).expect("nil is a sign-extended imm32");
                        for slot in (at + *returned as usize)..end {
                            dynasm!(ops
                                ; .arch x64
                                ; mov QWORD [r13 + (slot * 8) as i32], nil
                            );
                        }
                        dynasm!(ops
                            ; .arch x64
                            ; mov rax, QWORD r12 => RunState.base
                            ; add rax, end as i32
                            ; mov QWORD r12 => RunState.top, rax
                        );
                    }
                },
                Residual::Arrive { a, c } => {
                    // The call's results, taken by `Arrive`, which keeps no register
                    // but `state`'s: the base pointer is loaded again. See Note
                    // [Returns] in `specialize`.
                    let hold = |count: u16| crate::specialize::Count::hold(count) as u64;
                    let arrive = frame_op!(Arrive [] (hold(*a) | hold(*c) << 16); *a, *c);
                    emit_frame_op(ops, &mut self.jctx.stencils, pool, &arrive);
                    self.jctx.frame_ops.push(arrive);
                    dynasm!(ops
                        ; .arch x64
                        ; mov r13, QWORD [rsp - 0]
                    );
                },
                Residual::Jump(target) => {
                    // If the block ends in a jump, and the block hasn't already been emitted, then
                    // we can elide a jump and instead fallthrough. We will use the target as
                    // `successor`, and so the JIT worklist will compile it immediately after this
                    // code.
                    emit_jump(ops, &alloc, target,
                        off == end - 1 && self.jctx.blocks.get(target).is_none(), false);
                    successor = Some(*target);
                },
                Residual::Ret(pc, a, b, closes, vararg, returns, effects) => {
                    // The frame, popped by `PopFrame`, and the JIT code left with the
                    // return (`RETURNED | effects << EFFECTS_SHIFT | id`), or for the
                    // outermost frame's, the exit. See Notes [Frame ops], [Call
                    // continuations] and [Call effects] in `specialize`.
                    let hold = crate::specialize::Count::hold;
                    // With the id of what it returns. See Note [Call continuations] in `specialize`.
                    let (held_a, held_b, returns) = (hold(*a as u16), hold(*b), *returns);
                    let (effects, at) = (*effects as u64, Location(BlockId(id.0), off).pack().bits() as u64);
                    let pop = match (*closes, *vararg) {
                        (false, false) => frame_op!(PopFrame [false, false,] (held_a, held_b, returns, effects, at); *a as u16, *b),
                        (false, true) => frame_op!(PopFrame [false, true,] (held_a, held_b, returns, effects, at); *a as u16, *b),
                        (true, false) => frame_op!(PopFrame [true, false,] (held_a, held_b, returns, effects, at); *a as u16, *b),
                        (true, true) => frame_op!(PopFrame [true, true,] (held_a, held_b, returns, effects, at); *a as u16, *b),
                    };
                    jit_note!(self.jctx, ops, "        PopFrame");
                    emit_frame_op(ops, &mut self.jctx.stencils, pool, &pop);
                    self.jctx.frame_ops.push(pop);
                    jit_note!(self.jctx, ops, "        leave, with what it returned");
                    dynasm!(ops
                        ; .arch x64
                        ; mov rax, QWORD r12 => RunState.exit
                        ; jmp ->exit_jit
                    );
                },
                Residual::Branch { hot, cold } => {
                    match fused.take() {
                        // The op falls through to exit 0, the hot way; exit 1, its cold
                        // path's, goes off the hot path. See Notes [Window exits] in
                        // `window` and [Optimistic ops] in `specialize`.
                        Some((label, aligned, _)) => {
                            let (moves, to, count) = emit_jump(ops, &alloc, cold, false, true).expect("a deferred jump's moves");
                            pool.stubs.push((label, Stub::Way { aligned, moves, to, count }));
                            emit_jump(ops, &alloc, hot, self.jctx.blocks.get(hot).is_none(), false);
                        },
                        // An op run by its body on the stack, which selected.
                        None => {
                            dynasm!(ops
                                ; cmp QWORD r12 => RunState.select, 0
                                ; jnz >cold_way
                            );
                            emit_jump(ops, &alloc, hot, false, false);
                            dynasm!(ops ; cold_way:);
                            emit_jump(ops, &alloc, cold, false, false);
                        },
                    }
                    successor = Some(*hot);
                },
                // The op before it took exit 0, falling through, or exit 1 to its
                // way. See Note [Window exits] in `window`.
                Residual::Select(targets) if fused.is_some() => {
                    let (label, aligned, fall_exit) = fused.take().expect("a fused exit");
                    let first = targets[0].1;
                    if fall_exit == 1 {
                        // As the test of `select` would be laid out: exit 1's way after
                        // the op, exit 0 past it to the first target, laid out next.
                        emit_jump(ops, &alloc, &targets[1].1, false, false);
                        dynasm!(ops ; .arch x64 ; =>label);
                        if aligned {
                            dynasm!(ops ; .arch x64 ; add rsp, 8);
                        }
                    } else {
                        // Exit 1 comes only from its cold path: its way off the hot path.
                        let (moves, to, count) = emit_jump(ops, &alloc, &targets[1].1, false, true).expect("a deferred jump's moves");
                        pool.stubs.push((label, Stub::Way { aligned, moves, to, count }));
                    }
                    emit_jump(ops, &alloc, &first, self.jctx.blocks.get(&first).is_none(), false);
                    successor = Some(first);
                },
                Residual::Select(targets) => {
                    dynasm!(ops
                        ; mov rax, QWORD r12 => RunState.select
                    );
                    // A taken target's transfer may use rax (`SCRATCH`): the
                    // comparisons only continue on the paths not taken.
                    //
                    // `select` is always one of the targets: debug builds test
                    // each and trap on anything else, which release builds
                    // trust, testing only the targets after the first and
                    // falling through to it.
                    let tested = if cfg!(debug_assertions) { 0 } else { 1 };
                    for (i, target) in targets.iter().enumerate().skip(tested) {
                        #[cfg(feature = "align_selects")]
                        if (self.jctx.region_base + ops.offset().0) % CACHE_LINE + SELECT_TEST > CACHE_LINE {
                            pad(ops, self.jctx.region_base, CACHE_LINE);
                        }
                        let test = ops.offset().0;
                        dynasm!(ops
                            ; cmp rax, i as i32
                            ; jnz >next_target
                        );
                        debug_assert_eq!(ops.offset().0 - test, SELECT_TEST, "a Select's test");
                        emit_jump(ops, &alloc, &target.1, false, false);
                        dynasm!(ops
                            ; next_target:
                        );
                    }
                    if cfg!(debug_assertions) {
                        dynasm!(ops
                            ; ud2
                        );
                    } else {
                        // The first target is laid out next if it isn't compiled
                        // yet, as a `Jump`'s is: falling through, it needs no jump.
                        debug_assert_eq!(off, block.instructions.len() - 1, "a Select ends its block");
                        let first = targets[0].1;
                        emit_jump(ops, &alloc, &first, self.jctx.blocks.get(&first).is_none(), false);
                        successor = Some(first);
                    }
                },
                Residual::GC => {
                    dynasm!(ops
                        ; .arch x64
                        ; call extern (JitHelper::gc_safepoint as *const () as usize)
                    );
                },
                Residual::ExecWindow(w) | Residual::GuardDynamic(w) => {
                    // The op copied for it, as planning placed. See Note [Unboxed
                    // doubles] in `window_alloc`.
                    let w = self.jctx.stencils.effective(w);
                    let w = &w;
                    let stencils = &mut self.jctx.stencils;
                    let emits = match plans.get(&id) {
                        Some(plan) => plan.placed[off].map(|(skip, want)| {
                            let mut emits = alloc.reconcile(&want.unpack(), &**w, skip as usize);
                            emits.extend(alloc.op(&**w, [skip as usize]).expect("a placed op runs at its SKIP"));
                            emits
                        }),
                        // Streaming: the op picks its `SKIP` from the window it finds.
                        None => {
                            alloc.op(&**w, usable_skips(stencils, &**w))
                        }
                    };
                    // How its exits are laid out: a guard falls through to its failure
                    // edge, exit 1 jumping to its pass edge; before a `Select` it falls
                    // through to exit 1's way, as the test of `select` would, when its
                    // stencil can (exit 1 only from its cold path otherwise); before a
                    // `Branch`, to exit 0, the hot way. See Note [Window exits] in
                    // `window`.
                    let next = block.instructions.get(off + 1);
                    let fuses = match next {
                        Some(Residual::Branch { .. }) => true,
                        Some(Residual::Select(targets)) => targets.len() == EXITS,
                        _ => false,
                    };
                    let fall_exit = match next {
                        Some(Residual::Select(_)) if fuses && w.exit1().is_some() => 1,
                        _ => 0,
                    };
                    let (other, unalign) = match res {
                        Residual::GuardDynamic(_) => (Some(insts[off + 2]), Unalign::Inline),
                        _ if w.selects() => (Some(ops.new_dynamic_label()), Unalign::Target),
                        _ => (None, Unalign::Target),
                    };
                    let mut copied = None;
                    match emits {
                        Some(emits) => {
                            let counted = window_count!(self.jctx, ops, emits);
                            window_dump!(self.jctx, "      {}{counted}", emits_line(&emits));
                            for emit in emits {
                                match emit {
                                    Emit::Op { skip } => {
                                        let body = stencils.body(&**w, skip, fall_exit).expect("a usable skip");
                                        splat(ops, &body, w.name(), &w.captures(), pool, other, unalign);
                                        copied = Some(body.aligned);
                                    }
                                    emit => emit_window_move(ops, emit),
                                }
                            }
                        }
                        // No stencil to copy: call the op's body on the stack.
                        None => {
                            let stores = alloc.flush();
                            let counted = window_count!(self.jctx, ops, stores);
                            window_dump!(self.jctx, "      no stencil: flush {}, then call window_interp{counted}", emits_line(&stores));
                            for emit in stores {
                                emit_window_move(ops, emit);
                            }
                            let (op, vtable) = (Rc::as_ptr(w) as *const dyn Window).to_raw_parts();
                            let vtable: *const () = unsafe { core::mem::transmute(vtable) };
                            dynasm!(ops
                                ; .arch x64
                                ; mov rdi, r12 // state
                                ; mov rsi, QWORD (op as i64)
                                ; mov rdx, QWORD (vtable as i64)
                                ; call extern (JitHelper::window_interp as *const () as usize)
                            );
                        }
                    }
                    match (res, other, copied) {
                        // Its body ran on the stack, and selected: as an inline guard, a
                        // pass jumps to `off + 2`, a failure falls through to `off + 1`,
                        // both with the window live.
                        (Residual::GuardDynamic(_), _, None) => {
                            #[cfg(feature = "align_selects")]
                            if (self.jctx.region_base + ops.offset().0) % CACHE_LINE + GUARD_TEST > CACHE_LINE {
                                pad(ops, self.jctx.region_base, CACHE_LINE);
                            }
                            let test = ops.offset().0;
                            dynasm!(ops
                                ; .arch x64
                                ; cmp QWORD r12 => RunState.select, 1
                                ; jz =>insts[off + 2]
                            );
                            debug_assert_eq!(ops.offset().0 - test, GUARD_TEST, "a GuardDynamic's test");
                        }
                        (Residual::GuardDynamic(_), ..) => {}
                        (_, Some(label), Some(aligned)) if fuses => fused = Some((label, aligned, fall_exit)),
                        // Selected, for whatever reads `select` after it.
                        (_, Some(label), Some(aligned)) => {
                            let join = ops.new_dynamic_label();
                            pool.stubs.push((label, Stub::Select { aligned, exit: 1, join }));
                            dynasm!(ops
                                ; .arch x64
                                ; mov QWORD r12 => RunState.select, 0
                                ; =>join
                            );
                        }
                        _ => {}
                    }
                },
                Residual::Thunk(_) => {
                    // Room for a `jmp rel32` past the exit, once the thunk is a
                    // jump. See Note [Thunk patching].
                    self.jctx.region_sites.push((id, off, ops.offset().0, alloc.cache().clone()));
                    ops.extend(&NOP5);
                    let stores = alloc.stores();
                    let counted = window_count!(self.jctx, ops, stores);
                    window_dump!(self.jctx, "      exit after {}{counted}", emits_line(&stores));
                    // See Note [Snapshots].
                    let snapshot = pool.snapshot(ops, Location(id, off), stores);
                    dynasm!(ops
                        ; .arch x64
                        ; lea rax, [=>snapshot]
                        ; jmp extern self.jctx.exit_snapshot
                    );
                },
                _ => {
                    emit_bailout(ops, off)
                }
            }; break; }
            window_dump!(self.jctx, "      window {}", alloc.cache());
        }

        (entry, successor)
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    /// Equal values share one pool entry; each address gets its own.
    #[test]
    fn pool_dedups_values() {
        let mut ops = Assembler::new(0);
        let mut pool = Pool::default();
        let a = pool.value(&mut ops, 7);
        let b = pool.value(&mut ops, 9);
        assert_eq!(pool.value(&mut ops, 7), a);
        assert_ne!(a, b);
        let fall = ops.new_dynamic_label();
        assert_ne!(pool.address(&mut ops, fall), pool.address(&mut ops, fall));
        assert_eq!(pool.entries.len(), 4);
    }
}
