#![allow(unused_parens)]
use std::io::Write;
use std::rc::Rc;
use std::cell::Cell;
use std::collections::{HashMap, HashSet, BTreeMap};
use crate::{Owner, TLCell, TlcOwner};
use crate::vm::{BlockId, LBoxed, LClosure, LType, LValue, PackedLocation, ReturnLocation, RunState, Tc, Vm};
use crate::gc::{GcInner, GcCtx};
use crate::lboxed::NClosureCell;
use crate::stack::ValueStack;
use crate::generator::{Block, Context, Residual, Specializer, SubPc};
use crate::window::{stencil_body, Access, Body, Captures, Image, NextRef, StencilError, Window, WINDOW};
use crate::window_alloc::{Above, Cache, Emit, Placement, WindowAlloc};
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

pub type JitExec = for<'a, 'src, 'intern> extern "rust-preserve-none" fn(&mut Owner, &'a mut RunState<'src, 'intern>, *const LBoxed<'src, 'intern>) -> u64;

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

pub struct JitHelper;
impl JitHelper {
    pub unsafe extern "C" fn check_guard(state: *mut (), idx: usize, expected: u8) -> bool {
        unsafe {
            //println!("state {:?} idx {} {}", state, idx, expected);
            let state = state as *mut RunState;
            let rs = &*state;
            let val = &rs.vals[rs.base + idx];
            (val.unbox().typeof_() as u8) == expected
        }
    }
    pub unsafe extern "C" fn check_epoch(state: *mut (), tab: usize, href: u8) -> bool {
        unsafe {
            //println!("state {:?} {} {}", state, tab, href);
            let state = state as *mut RunState;
            // Forge an owner
            let mut owner = ();
            let owner = (&raw mut owner as *mut Owner).as_ref_unchecked();
            let rs = &*state;
            let hwit = rs.hash_witnesses[rs.witness_base + href as usize].as_ref().unwrap();
            let tab_val = rs.vals[rs.base + tab].unbox();
            let LValue::Table(tab) = tab_val else { unreachable!() };
            debug!("JIT check_epoch sees {} == {}", hwit.epoch, tab.ro(owner).epoch);
            hwit.epoch == tab.ro(owner).epoch
        }
    }
    pub unsafe extern "C" fn check_hash_guard(state: *mut (), tab: usize, href: u8, expected: u8) -> bool {
        unsafe {
            let state = state as *mut RunState;
            // Forge an owner
            let mut owner = ();
            let owner = (&raw mut owner as *mut Owner).as_ref_unchecked();
            let rs = &*state;
            let hwit = rs.hash_witnesses[rs.witness_base + href as usize].as_ref().unwrap();
            let tab_val = rs.vals[rs.base + tab].unbox();
            let LValue::Table(tab) = tab_val else { unreachable!() };
            let Some((key, val)) = tab.ro(owner).hash.get_index(hwit.index) else { unreachable!() };
            (val.unbox().typeof_() as u8) == expected
        }
    }

    /// Run a window op whose stencil the copier rejected, through its
    /// interpreter path: operands from their stack homes, outputs flushed.
    pub unsafe extern "C" fn window_interp(owner: *mut (), state: *mut (), op: *const (), vtable: *const ()) {
        unsafe {
            let op: *const dyn Window = core::ptr::from_raw_parts(op, core::mem::transmute(vtable));
            let owner = &mut *(owner as *mut Owner);
            let state = &mut *(state as *mut RunState<'static, 'static>);
            (*op).interp(owner, state);
        }
    }

    /// Incremental GC safepoint from JIT'd code. The roots (state + specializer)
    /// were published before entering the JIT and the value stack is mutated in
    /// place, so `step_published` traces the live state. See Note [GC roots].
    pub unsafe extern "C" fn gc_safepoint(owner: *mut ()) {
        unsafe {
            let owner = &*(owner as *const Owner);
            GcCtx::assume_rooted().step_published(owner);
        }
    }

    pub unsafe extern "C" fn lua_return(state: *mut (), a: u16, b: u16, base_ptr: *const ()) -> u64 {
        unsafe {
            let rs = &mut *(state as *mut RunState);
            warn!("lua_return base {base} base_ptr {base_ptr:p} stack_ptr {stack_ptr:p}", base = rs.base, stack_ptr = rs.vals.stack_ptr.as_non_null_ptr());
            #[cfg(debug_assertions)]
            assert_eq!(base_ptr, rs.vals.stack_ptr.as_non_null_ptr().add(rs.base).as_ptr().cast());
            let mut owner = ();
            let mut owner = (&raw mut owner as *mut Owner).as_mut_unchecked();
            match rs.do_return(owner, a as usize, b as usize) {
                Ok(ReturnLocation::Interpreter(caller)) => {
                    // Bailout and return to interpreter
                    debug!("returning to {}", caller);
                    rs.trap = true;
                    return ((-5i32 as u64) << 32);
                }
                Ok(ReturnLocation::Generator(block, off)) => {
                    // Return block and offset
                    debug!("returning to {:?} {}", block, off);
                    return ((off as u64) << 32) | (block.0 as u64);
                }
                Err(r_vals) => {
                    panic!();
                    // Done
                    // TODO: Ugh we probably need to stash these r_vals somewhere instead of
                    // forgetting them. This would show up if we tailcall return through a JIT
                    // function to the top-level.
                    rs.trap = true;
                    return ((-5i32 as u64) << 32);
                }
            }
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

/// Allocator code as one line, for `window_dump!`.
#[cfg(feature = "window_dump")]
fn emits_line(emits: &[Emit]) -> String {
    emits.iter().map(ToString::to_string).collect::<Vec<_>>().join("; ")
}

/// The window registers `w0..w7` in the order the stencil ABI passes them (the
/// `rust-preserve-none` arguments after owner, state and base in r12, r13, r14),
/// then `SCRATCH`: rax, which every stencil clobbers (LLVM loads its `become`
/// target into it), so it only holds a value within one sequence of moves.
const WINDOW_REGS: [u8; WINDOW + 1] = [
    15, /* r15 */ 7, /* rdi */ 6, /* rsi */ 2, /* rdx */ 1, /* rcx */
    8, /* r8 */ 9, /* r9 */ 11, /* r11 */ 0, /* rax */
];

/// An 8-byte entry of the pool emitted after a compiled region's code.
enum PoolEntry {
    Value(u64),
    /// The absolute address of a label.
    Address(DynamicLabel),
}

/// The pool of a compiled region: its entries in order, each equal value once.
#[derive(Default)]
struct Pool {
    entries: Vec<(DynamicLabel, PoolEntry)>,
    values: HashMap<u64, DynamicLabel, FxBuildHasher>,
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
}

/// Window-op stencils copied out of this executable, by stencil address.
#[derive(Default)]
pub struct Stencils {
    image: Option<Result<Image, StencilError>>,
    bodies: HashMap<usize, Result<Rc<Body>, StencilError>, FxBuildHasher>,
}

impl Stencils {
    fn body(&mut self, op: &dyn Window, skip: usize) -> Result<Rc<Body>, StencilError> {
        let image = self.image.get_or_insert_with(Image::load).as_ref().map_err(Clone::clone)?;
        self.bodies
            .entry(op.stencil(skip))
            .or_insert_with(|| {
                unsafe { stencil_body(image, op, skip) }
                    .map(Rc::new)
                    .inspect_err(|e| warn!("window op not copied, calling its body instead: {e}"))
            })
            .clone()
    }
}

/// Emit an allocator instruction other than `Emit::Op`.
fn emit_window_move(ops: &mut Assembler, emit: Emit) {
    let reg = |r: usize| WINDOW_REGS[r];
    match emit {
        Emit::Load { reg: r, slot } => dynasm!(ops
            ; .arch x64
            ; mov Rq(reg(r)), QWORD [r14 + (slot * 8) as i32]
        ),
        Emit::Store { slot, reg: r } => dynasm!(ops
            ; .arch x64
            ; mov QWORD [r14 + (slot * 8) as i32], Rq(reg(r))
        ),
        Emit::Move { dst, src } => dynasm!(ops
            ; .arch x64
            ; mov Rq(reg(dst)), Rq(reg(src))
        ),
        // An op is splatted by the caller.
        Emit::Op { .. } => unreachable!(),
    }
}

/// Copy a stencil body into the code: holes are repointed at pool entries with
/// the op's captures, references to the op's continuation at the copy's end, and
/// every other RIP-relative reference at its original target. The body is entered
/// with the stack aligned as just after a call, as it was compiled to expect.
fn splat(ops: &mut Assembler, body: &Body, captures: &Captures, pool: &mut Pool) {
    enum Site {
        Value(u64),
        Absolute(usize),
        Fall,
        FallAddress,
    }
    let mut sites: SmallVec<[(usize, usize, Site); 8]> = SmallVec::new();
    sites.extend(body.holes.iter().map(|&(r, i)| (r.end, r.field, Site::Value(captures[i]))));
    sites.extend(body.relocations().iter().map(|r| (r.end, r.field, Site::Absolute(r.target))));
    sites.extend(body.nexts.iter().map(|n| match *n {
        NextRef::Direct(r) => (r.end, r.field, Site::Fall),
        NextRef::Indirect(r) => (r.end, r.field, Site::FallAddress),
    }));
    sites.sort_by_key(|&(end, ..)| end);

    let rel32 = |kind| dynasmrt::x64::X64Relocation::from_size(kind, RelocationSize::DWord);
    let fall = ops.new_dynamic_label();
    dynasm!(ops ; .arch x64 ; sub rsp, 8);
    let mut at = 0;
    for (end, field, site) in sites {
        ops.extend(&body.code[at..end]);
        at = end;
        let field_offset = (end - field) as u8;
        match site {
            Site::Absolute(target) => ops.value_relocation(target, field_offset, 0, rel32(RelocationKind::RelToAbs)),
            Site::Fall => ops.dynamic_relocation(fall, 0, field_offset, 0, rel32(RelocationKind::Relative)),
            Site::Value(value) => {
                let entry = pool.value(ops, value);
                ops.dynamic_relocation(entry, 0, field_offset, 0, rel32(RelocationKind::Relative));
            }
            Site::FallAddress => {
                let entry = pool.address(ops, fall);
                ops.dynamic_relocation(entry, 0, field_offset, 0, rel32(RelocationKind::Relative));
            }
        }
    }
    ops.extend(&body.code[at..]);
    dynasm!(ops ; .arch x64 ; =>fall ; add rsp, 8);
}

const JIT_SIZE: usize = 0x1000 * 16;
pub struct JitContext {
    pub memory: std::cell::Cell<dynasmrt::mmap::ExecutableBuffer>,
    pub blocks: HashMap<BlockId, JitBlock, FxBuildHasher>,
    pub pending: BTreeMap<BlockId, Pending>,
    pub stencils: Stencils,
    pub used: usize,
    pub perf_map: Option<std::cell::RefCell<std::fs::File>>,
    pub window_dump: Option<std::cell::RefCell<std::fs::File>>,
}

#[derive(Copy, Clone)]
struct JitPtr(*const u8);

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

/// Where the backward pass placed a block's window ops. See Note [Window
/// allocation].
pub struct BlockPlan {
    /// The registers of its entry window: the slots it and its successors read
    /// before writing, where they read them.
    entry: Placement,
    /// Per residual, for a window op with a stencil: its `SKIP` and the placement
    /// it wants before it.
    ops: Vec<Option<(usize, Placement)>>,
}

type Plans = HashMap<BlockId, BlockPlan, FxBuildHasher>;

/// A type guard tested inline, in the window register caching its slot.
fn inline_guard(res: &Residual) -> bool {
    matches!(res, Residual::Guard { expected: LType::Number | LType::Nil | LType::Bool | LType::Table | LType::Closure | LType::String, .. })
}

/// The blocks a residual jumps to.
fn jump_targets(res: &Residual) -> SmallVec<[BlockId; 2]> {
    match res {
        Residual::Jump(target) => smallvec::smallvec![*target],
        Residual::Select(targets) => targets.iter().map(|target| target.1).collect(),
        _ => SmallVec::new(),
    }
}

impl JitContext {
    pub fn new() -> Self {
        let near = Self::find_near();
        assert!(near != core::ptr::null_mut());
        let mut memory = dynasmrt::mmap::MutableBuffer::new_with_hint(JIT_SIZE, near).unwrap();
        debug!("allocated JIT memory @ {:?}", memory.as_ptr());
        // Set the JIT memory to the max size initially, so that we don't need to
        // mprotect back to mutable just to reserve
        memory.set_len(JIT_SIZE);
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
        Self {
            memory: Cell::new(memory.make_exec().unwrap()),
            blocks: HashMap::default(),
            pending: BTreeMap::new(),
            stencils: Stencils::default(),
            used: 0,
            perf_map,
            window_dump,
        }
    }

    pub fn add_to_perf_map(&self, addr: usize, size: usize, name: &str) {
        #[cfg(feature = "perf")]
        if let Some(ref map) = self.perf_map {
            let mut map = map.borrow_mut();
            writeln!(map, "{:x} {:x} {}", addr, size, name).ok();
        }
    }

    fn find_near() -> *mut core::ffi::c_void {
        let target = JitHelper::check_guard as *mut u8 as usize;
        let MAX_DIST = 2isize.pow(31);
        let maps = rsprocmaps::from_path("/proc/self/maps").unwrap();
        // Our goal is to find an available place in memory such that our entire JIT_SIZE buffer is
        // within 2GB of the target.
        // This means that we can
        // 1) allocate memory before it, with a start <2GB away, and a JIT_SIZE hole
        // 2) allocate memory after it, with a start <2GB-JIT_SIZE away, and a JIT_SIZE hole
        // Really this needs to have the target be a *range* and require a buffer that is within
        // distance of both the start and end, and then we should compute the start and end based
        // off all of our closure call targets...but it isn't likely to matter, so we don't.
        let res = maps.map_windows(|[first, second]| {
            let (Ok(first), Ok(second)) = (first, second) else { return None };
            // Case 1
            if (target as isize - first.address_range.end as isize).abs() < MAX_DIST && (second.address_range.begin - first.address_range.end) as usize >= JIT_SIZE {
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
        #[cfg(debug_assertions)]
        assert!(self.used + len < JIT_SIZE);
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
}

impl<'src, 'intern> Specializer<'src, 'intern> {
    pub fn jit_compile(&mut self, id: BlockId, owner: &mut Owner) {
        debug!("JIT compiling block {:?}", id);
        window_dump!(self.jctx, "== region entered at block {}", id.0);
        let base = self.jctx.end();
        let mut ops = dynasmrt::VecAssembler::<dynasmrt::x64::X64Relocation>::new(base.0 as usize);
        let entry = ops.offset();

        // SystemV ABI is RDI, RSI, RDX, RCX, R8, R9
        // JitExec (rust-preserve-none): R12=owner, R13=state, R14=base_ptr, R15=base_ptr

        dynasm!(ops
            ; .arch x64
            ; push rbp
            ; mov rbp, rsp
            ; push rbx
            ; push r14 // save initial base_ptr
        );
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
            window_dump!(self.jctx, "block {} compiled already, entered with {}: {}", id.0, block.window, emits_line(&loads));
            for emit in loads {
                emit_window_move(&mut ops, emit);
            }
            dynasm!(ops
            ; jmp extern block.ptr.0 as usize
            );
        } else {
            plans = self.plan_region(id);
            // Load the window the block is entered with, clean from the stack.
            let window = Cache::entry(plans[&id].entry, &Cache::default());
            let loads = WindowAlloc::default().transfer(&window);
            window_dump!(self.jctx, "region entry block {} loads {}", id.0, emits_line(&loads));
            for emit in loads {
                emit_window_move(&mut ops, emit);
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

        let epilogue = ops.offset();
        dynasm!(ops
            ; .arch x64
            ; ->exit_jit:
            ; pop r14
            ; pop rbx
            ; pop rbp
            ; ret
        );
        self.jctx.reserve(ops.offset().0 - epilogue.0);

        let pool_start = ops.offset();
        ops.align(8, 0xcc);
        for (label, entry) in pool.entries {
            let value = match entry {
                PoolEntry::Value(value) => value,
                PoolEntry::Address(target) => {
                    let offset = ops.labels().resolve_dynamic(target).expect("pool entry for a placed label");
                    (base.0 as usize + offset.0) as u64
                }
            };
            dynasm!(ops ; =>label);
            ops.extend(&value.to_le_bytes());
        }
        self.jctx.reserve(ops.offset().0 - pool_start.0);

        debug!("drained pending");
        let buf = ops.finalize().unwrap();
        let Some(slab) = self.jctx.commit(base, buf.as_slice()) else { panic!() };
        let entrypoint: JitExec = unsafe { core::mem::transmute(slab.add(entry.0)) };

        let (source, line) = {
            let proto = self.clos.ro(owner).prototype;
            let source = unsafe { String::from_utf8_lossy((*proto).source.data).to_string().replace("\0", "") };
            let line = unsafe { (*proto).line_defined };
            (source, line)
        };

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
    }

    /// Plan the window allocation of the region compiled from `entry`: the blocks
    /// reachable from it not compiled yet, each placed bottom-up in a depth-first
    /// postorder, so after its successors except across the edge closing a
    /// cycle. See Note [Window allocation].
    fn plan_region(&mut self, entry: BlockId) -> Plans {
        let targets = |block: BlockId| -> SmallVec<[BlockId; 4]> { self.blocks[block.0].instructions.iter().flat_map(jump_targets).collect() };
        let mut postorder = Vec::new();
        let mut seen: HashSet<BlockId, FxBuildHasher> = HashSet::default();
        seen.insert(entry);
        let mut stack = vec![(entry, targets(entry), 0)];
        while let Some((block, successors, next)) = stack.last_mut() {
            match successors.get(*next).copied() {
                Some(target) => {
                    *next += 1;
                    if !self.jctx.blocks.contains_key(&target) && seen.insert(target) {
                        stack.push((target, targets(target), 0));
                    }
                }
                None => {
                    postorder.push(*block);
                    stack.pop();
                }
            }
        }
        let mut plans = Plans::default();
        for block in postorder {
            let plan = self.plan_block(block, &plans);
            plans.insert(block, plan);
        }
        plans
    }

    /// Place a block's window ops bottom-up, from the entry window of its hottest
    /// successor planned (or compiled) already as its live-out: of equally hot
    /// ones, a later jump's before an earlier one's, and a select's first target.
    fn plan_block(&mut self, id: BlockId, plans: &Plans) -> BlockPlan {
        let block = &self.blocks[id.0];
        let blocks = &self.blocks;
        let compiled = &self.jctx.blocks;
        let stencils = &mut self.jctx.stencils;
        let live_out = block
            .instructions
            .iter()
            .rev()
            .flat_map(jump_targets)
            .filter_map(|target| match compiled.get(&target) {
                Some(done) => Some((target, *done.window.regs())),
                None => plans.get(&target).map(|plan| (target, plan.entry)),
            })
            .min_by_key(|&(target, _)| blocks[target.0].jit_info.hotness.get());
        // The usable `SKIP`s of each window op; one with none is called, a flush.
        let skips: Vec<SmallVec<[usize; WINDOW]>> = block
            .instructions
            .iter()
            .map(|res| match res {
                Residual::ExecWindow(w) => (0..=WINDOW - w.arity()).filter(|&skip| stencils.body(&**w, skip).is_ok()).collect(),
                _ => SmallVec::new(),
            })
            .collect();
        let flushes = |off: usize| match &block.instructions[off] {
            Residual::ExecWindow(_) => skips[off].is_empty(),
            Residual::Jump(_) | Residual::Select(_) | Residual::Thunk(_) => false,
            res => !inline_guard(res),
        };
        // The slots a residual reads and writes from the window: a window op's
        // operands, and the slot an inline guard tests.
        let operands = |res: &Residual| -> SmallVec<[(usize, Access); WINDOW]> {
            match res {
                Residual::ExecWindow(w) => w.operands().iter().copied().zip(w.accesses().iter().copied()).collect(),
                Residual::Guard { idx, .. } if inline_guard(res) => smallvec::smallvec![(*idx, Access::Read)],
                _ => SmallVec::new(),
            }
        };
        // Per slot and access, how many residuals before `end`, since the flush
        // before it, use it so; and whether that reaches the block's start, where
        // a value can arrive in a register instead of from the stack.
        let uses_before = |end: usize| {
            let mut uses: HashMap<(usize, Access), usize, FxBuildHasher> = HashMap::default();
            let mut entered = true;
            for off in (0..end).rev() {
                if flushes(off) {
                    entered = false;
                    break;
                }
                for operand in operands(&block.instructions[off]) {
                    *uses.entry(operand).or_default() += 1;
                }
            }
            (uses, entered)
        };
        let alloc = WindowAlloc::default();
        let mut ops = vec![None; block.instructions.len()];
        let mut want: Placement = [None; WINDOW];
        let (mut uses, mut entered) = uses_before(block.instructions.len());
        for (off, res) in block.instructions.iter().enumerate().rev() {
            if let Some((target, entry)) = live_out {
                if jump_targets(res).contains(&target) {
                    want = entry;
                }
            }
            if !flushes(off) {
                for operand in operands(res) {
                    *uses.get_mut(&operand).expect("counted") -= 1;
                }
            }
            let count = |slot, access| uses.get(&(slot, access)).copied().unwrap_or(0);
            // Unused above the block's start, a slot is read from the block's
            // entry window, where the predecessor can leave it in a register.
            let above = |slot| match (count(slot, Access::Write), count(slot, Access::Read)) {
                (0, 0) if !entered => Above::Unused,
                (0, _) => Above::Read,
                _ => Above::Written,
            };
            match res {
                Residual::ExecWindow(w) if !skips[off].is_empty() => {
                    let (skip, before) = alloc.place(&**w, skips[off].iter().copied(), &want, above).expect("a usable SKIP");
                    ops[off] = Some((skip, before));
                    want = before;
                }
                // An inline guard tests its slot where the window has it: keep it
                // in a register, if one is free.
                Residual::Guard { idx, .. } if inline_guard(res) => {
                    if !want.contains(&Some(*idx)) {
                        if let Some(reg) = want.iter().position(Option::is_none) {
                            want[reg] = Some(*idx);
                        }
                    }
                }
                _ if flushes(off) => {
                    want = [None; WINDOW];
                    (uses, entered) = uses_before(off);
                }
                _ => {}
            }
        }
        BlockPlan { entry: want, ops }
    }

    /// JIT compile one block, returning the JIT code offset and optionally the next block to
    /// compile.
    pub fn jit_block(&mut self, id: BlockId, ops: &mut Assembler, pool: &mut Pool, owner: &mut Owner, plans: &Plans) -> (AssemblyOffset, Option<BlockId>) {
        // We try to bias the default exit as the next block to compile. This is only a suggestion,
        // and doesn't affect correctness; `GUARD; JMP failure; RET;` for example may say that
        // `failure` is the "next block" despite not quite being correct.
        let mut successor = None;
        let entry = ops.offset();
        let x = self.jctx.memory.get_mut().as_ptr();
        let block = &self.blocks[id.0];
        let insts: Vec<_> = block.instructions.iter().map(|_| ops.new_dynamic_label()).collect();
        let mut alloc = WindowAlloc::entering(self.jctx.blocks[&id].window.clone());
        window_dump!(self.jctx, "block {} hotness {} entered with {}", id.0, block.jit_info.hotness.get(), alloc.cache());

        // Jump to `target`, or fall through to it if `skip`, transferring the
        // window to the one it is entered with: its planned entry window, dirty where the
        // first jump to it compiled delivers it dirty.
        let mut emit_jump = |ops: &mut Assembler, alloc: &WindowAlloc, target: &BlockId, skip: bool| {
            if let Some(target_block) = self.jctx.blocks.get(target) {
                // We already JIT compiled the block, and can jump to it directly.
                let transfer = alloc.transfer(&target_block.window);
                window_dump!(self.jctx, "      to block {} (compiled, entered with {}): {}", target.0, target_block.window, emits_line(&transfer));
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
                    window: Cache::entry(plans[target].entry, alloc.cache()),
                });
                let transfer = alloc.transfer(&pending.window);
                window_dump!(self.jctx, "      to block {} (entered with {}): {}", target.0, pending.window, emits_line(&transfer));
                for emit in transfer {
                    emit_window_move(ops, emit);
                }
                if !skip {
                    dynasm!(ops
                        ; jmp =>pending.label
                    );
                }
            }
        };

        let emit_bailout = |ops: &mut Assembler, off| {
            if off == 0 {
                // If we're trying to bailout from the first instruction, we
                // need to record it as a JIT exit so that we don't try to call
                // this same function again immediately in a loop.
                dynasm!(ops
                    ; .arch x64
                    ; mov WORD r13 => RunState.current_off, (off as i16)
                    ; mov rax, QWORD (((-1i32 as u64) << 32 | (id.0 as u64)) as i64)
                    ; mov BYTE r13 => RunState.trap, 1
                    ; jmp ->exit_jit
                );
            } else {
                // Fallback to interpreter for other residuals
                dynasm!(ops
                    ; .arch x64
                    ; mov rax, QWORD (((off as u64) << 32 | (id.0 as u64)) as i64)
                    ; mov BYTE r13 => RunState.trap, 1
                    ; jmp ->exit_jit
                );
            }
        };

        // Charge `cost` residuals of gas at residual `off`, exiting if it runs out
        // (after `stores`, which bring the stack up to date with the window).
        #[cfg(feature = "gas")]
        let emit_gas_check = |ops: &mut Assembler, off: usize, cost: usize, stores: &[Emit]| {
            dynasm!(ops
                ; sub QWORD r13 => RunState.gas, cost as i32
                ; mov WORD r13 => RunState.current_off, (off as i16)
                ; ja >have_gas
            );
            for &emit in stores {
                emit_window_move(ops, emit);
            }
            dynasm!(ops
                ; mov rax, QWORD (((-1i32 as u64) << 32 | (id.0 as u64)) as i64)
                ; mov BYTE r13 => RunState.trap, 1
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
        // gets no label, so a jump to one fails to assemble.
        let window = |r: &Residual| matches!(r, Residual::ExecWindow(_));
        let jump = |r: &Residual| matches!(r, Residual::Jump(_) | Residual::Select(_));
        for (off, res) in block.instructions.iter().enumerate() {
            debug!("JIT operation {res:?}");
            window_dump!(self.jctx, "  {off:3} {res}");
            let prev = off.checked_sub(1).map(|p| &block.instructions[p]);
            let keeps_window = window(res) || inline_guard(res) || jump(res) || matches!(res, Residual::Thunk(_));
            if window(res) && prev.is_some_and(|p| window(p)) {
                // Inside a run of window residuals, charged for with its first.
            } else {
                let label = insts[off];
                dynasm!(ops
                    ; => label
                );
                if !keeps_window && !alloc.is_empty() {
                    let stores = alloc.flush();
                    window_dump!(self.jctx, "      flush: {}", emits_line(&stores));
                    for emit in stores {
                        emit_window_move(ops, emit);
                    }
                }
                #[cfg(feature = "gas")]
                emit_gas_check(ops, off, block.instructions[off..].iter().take_while(|r| window(r)).count().max(1), &alloc.stores());
            }
            loop { match res {
                Residual::Guard { idx, expected } if inline_guard(res) => {
                    // NuN-boxed type check of the value in `STACK[idx]`: in the window
                    // register caching it, or else loaded from its stack home. A
                    // *match* jumps to the success continuation at `off + 2`, a
                    // *mismatch* falls through to the failure edge at `off + 1`,
                    // both with the window live.
                    //
                    //   * Number   : the value has any `NUMBER_TAG` bit set.
                    //   * Nil/Bool : exact immediate compare (nil = 2, false/true = 6/7).
                    //   * cell types (Table/Closure/String): the value is a raw pointer
                    //     (no `NOT_CELL_MASK` bits) whose offset-0 header byte is the kind.
                    //     We must reject non-cells first so we never dereference a double
                    //     or an immediate.
                    //
                    // `v` holds the value: its window register, or else r10. rax,
                    // never a window register, is scratch for the masks.
                    let m = 0; // rax
                    window_dump!(self.jctx, "      tests {}",
                        alloc.register_of(*idx).map_or(format!("[{idx}]"), |reg| format!("w{reg}")));
                    let v = match alloc.register_of(*idx) {
                        Some(reg) => WINDOW_REGS[reg],
                        None => {
                            dynasm!(ops
                                ; .arch x64
                                ; mov r10, QWORD r14 => LBoxed<'src, 'intern>[*idx as i32]
                            );
                            10 // r10
                        }
                    };
                    match expected {
                        LType::Number => dynasm!(ops
                            ; .arch x64
                            ; mov Rq(m), QWORD (LBoxed::NUMBER_TAG as i64)
                            ; test Rq(v), Rq(m)
                            ; jnz =>insts[off + 2]
                        ),
                        LType::Nil => dynasm!(ops
                            ; .arch x64
                            ; cmp Rq(v), (LBoxed::VALUE_NIL as i32)
                            ; jz =>insts[off + 2]
                        ),
                        LType::Bool => dynasm!(ops
                            ; .arch x64
                            ; mov Rq(m), Rq(v)
                            ; or Rq(m), 1 // false(6) -> 7, true(7) -> 7
                            ; cmp Rq(m), (LBoxed::VALUE_TRUE as i32)
                            ; jz =>insts[off + 2]
                        ),
                        LType::Table => dynasm!(ops
                            ; .arch x64
                            ; mov Rq(m), QWORD (LBoxed::NOT_CELL_MASK as i64)
                            ; test Rq(v), Rq(m)
                            ; jnz >guard_fail // not a cell
                            ; cmp BYTE [Rq(v)], (LBoxed::KIND_TABLE as i8)
                            ; jz =>insts[off + 2]
                            ; guard_fail:
                        ),
                        LType::Closure => dynasm!(ops
                            ; .arch x64
                            ; mov Rq(m), QWORD (LBoxed::NOT_CELL_MASK as i64)
                            ; test Rq(v), Rq(m)
                            ; jnz >guard_fail // not a cell
                            ; movzx Rd(m), BYTE [Rq(v)]
                            ; sub Rd(m), (LBoxed::KIND_LCLOSURE as i32) // LClosure(2)/NClosure(3)
                            ; cmp Rd(m), 1
                            ; jbe =>insts[off + 2]
                            ; guard_fail:
                        ),
                        LType::String => dynasm!(ops
                            ; .arch x64
                            ; mov Rq(m), QWORD (LBoxed::NOT_CELL_MASK as i64)
                            ; test Rq(v), Rq(m)
                            ; jnz >guard_fail // not a cell
                            ; movzx Rd(m), BYTE [Rq(v)]
                            ; sub Rd(m), (LBoxed::KIND_OWNED as i32) // Owned(4)/Interned(5)
                            ; cmp Rd(m), 1
                            ; jbe =>insts[off + 2]
                            ; guard_fail:
                        ),
                        _ => unreachable!(),
                    }
                },
                Residual::Guard { idx, expected } => {
                    // A type with no inline test: ask `check_guard`. The window was
                    // flushed, since the call clobbers it.
                    let expected_u8 = *expected as u8;
                    dynasm!(ops
                        ; .arch x64
                        ; mov rdi, r13 // state
                        ; mov rsi, WORD (*idx as i32) // idx
                        ; mov rdx, WORD (expected_u8 as i32) // expected
                        ; call extern (JitHelper::check_guard as *const () as usize)
                        ; test al, al
                        ; jnz =>insts[off + 2]
                        // Fail: fallthrough to next (off + 1)
                    );
                },
                Residual::NativeGuard { idx, ptr } => {
                    // The value is a raw (leaked) `NClosureCell` pointer; load its
                    // `native` fn pointer and compare to the specialized target.
                    dynasm!(ops
                        ; .arch x64
                        ; mov rax, QWORD r14 => LBoxed<'src, 'intern>[*idx as i32]
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
                        ; mov rax, QWORD r14 => LBoxed<'src, 'intern>[*idx as i32]
                        ; lea rax, rax => GcInner<TLCell<TlcOwner, LClosure<'src, 'intern>>>.val
                        ; mov rcx, QWORD (*ptr as i64)
                        ; cmp rcx, QWORD rax => LClosure<'src, 'intern>.prototype
                        ; jz =>insts[off + 2]
                        // Fail: fallthrough to next (off + 1)
                    );
                },
                Residual::EpochCheck { tab, href } => {
                    let href_u8 = href.0;
                    dynasm!(ops
                        ; .arch x64
                        ; mov rdi, r13 // state
                        ; mov rsi, WORD (*tab as i32)
                        ; mov rdx, WORD (href_u8 as i32)
                        ; call extern (JitHelper::check_epoch as *const () as usize)
                        ; test al, al
                        ; jnz =>insts[off + 2]
                        // Fail: fallthrough to next (off + 1)
                    );
                },
                Residual::HashGuard { tab, href, expected } => {
                    let href_u8 = href.0;
                    let expected_u8 = *expected as u8;
                    dynasm!(ops
                        ; .arch x64
                        ; mov rdi, r13 // state
                        ; mov rsi, WORD (*tab as i32)
                        ; mov rdx, WORD (href_u8 as i32)
                        ; mov rcx, WORD (expected_u8 as i32)
                        ; call extern (JitHelper::check_hash_guard as *const () as usize)
                        ; test al, al
                        ; jnz =>insts[off + 2]
                        // Fail: fallthrough to next (off + 1)
                    );
                },
                Residual::Exec(f) => {
                    let (this_obj, this_vtable, this_call) = get_ptr_from_closure(f.body.as_ref());
                    debug!("JIT memory @ {:?}, operation @ {:#x}, desired {:?}", x, this_call, &mut JitHelper::check_guard as &mut _ as *mut _ as *mut core::ffi::c_void);
                    dynasm!(ops
                        ; .arch x64
                        ; mov rsi, r12 // owner
                        ; mov rdx, r13 // state
                        ; mov rdi, QWORD (this_obj as i64)
                        ; mov rax, QWORD (this_vtable as i64)
                        // Lua wants to see PC+1, and also we want to resume to PC+1 if we trap.
                        ; mov WORD r13 => RunState.current_off, ((off + 1) as i16)
                        ; call extern (this_call)
                        //// Check for trap
                        ; mov al, BYTE r13 => RunState.trap
                        ; test al, al
                        ; jz >no_trap
                        //// Trap 4 so specializer can handle it
                        ; mov rax, QWORD (((-1i32 as u64) << 32 | (id.0 as u64)) as i64)
                        ; jmp ->exit_jit
                        ; no_trap:
                    );
                },
                Residual::LuaCall { lclos, a, b, c } => {
                    // Look up a JIT block for the callee's entrypoint with no known types.
                    // Any miss (callee never specialized, no matching version, or not yet
                    // compiled) falls through to a bailout below.
                    let next_stack = unsafe { (*lclos.ro(owner).prototype).max_stack.into() };
                    let ctx = Rc::new(Context::new(vec![LType::Unknown; next_stack]));
                    let entry: Option<*const ()> = self.versions
                        .get(&lclos.ro(owner).prototype)
                        .and_then(|versions| versions.get(&(SubPc::new(0), ctx)))
                        .and_then(|block| self.blocks[block.0].jit_info.entry.map(|f| f as *const _));
                    match entry {
                        Some(entry) => {
                            // Return location for this call site, packed to a single word.
                            let packed_ret = ReturnLocation::Generator(BlockId(id.0), off + 1).pack();
                            // Pin the exact monomorphized address of the extern "C" call_lua.
                            let call_lua: extern "C" fn(&mut RunState<'src, 'intern>, &mut Owner, PackedLocation, u16, u16, u16) -> usize = RunState::call_lua;
                            dynasm!(ops
                                ; mov rdi, r13 // &mut RunState
                                ; mov rsi, r12 // owner
                                ; mov rdx, QWORD (packed_ret.bits() as i64)
                                ; mov rcx, WORD (*a as i32)
                                ; mov  r8, WORD (*b as i32)
                                ; mov  r9, WORD (*c as i32)
                                ; call extern (call_lua as *const () as usize)

                                // Reload r14 = callee base ptr = vals.stack_ptr + base*sizeof(LBoxed)
                                ; lea rcx, r13 => RunState.vals
                                ; mov rax, QWORD rcx => ValueStack<'src, 'intern>.stack_ptr
                                ; mov rcx, QWORD r13 => RunState.base
                                ; lea r14, [rax + rcx * 8]

                                // state is already in r13
                                ; call extern (entry as usize)
                                ; mov r14, QWORD [rsp - 0]

                                // Check if the call is trying to bailout: we propagate the bailout
                                // if so, unwinding our native stack but yielding to the generator run loop
                                // with a suspended ReturnLocation stack.
                                ; cmp BYTE r13 => RunState.trap, 0
                                ; jnz ->exit_jit

                                // Reload the correct base ptr for the remainder of our function
                            );
                        },
                        None => {
                            // TODO: we could emit a patchpoint and fill it in once the callee
                            // block is compiled; for now bail to the interpreter for good.
                            emit_bailout(ops, off)
                        },
                    }
                },
                Residual::NativeCall { nf, a, b, c } => {
                    // Native signature `fn(seq, args, returns, owner)` with ZST seq/owner,
                    // so the two `&[LBoxed]` slice views arrive as (rdi=args ptr, rsi=args
                    // len, rdx=returns ptr, rcx=returns len); r14 is `&vals[base]`. `a/b/c`
                    // are compile-time constants, so specialize the lengths per site: a
                    // fixed count when b/c are non-zero, else `vals.used - base - off` for
                    // the "to top-of-stack" (0) shape. Then call the native directly.
                    let (a, b, c) = (*a as i32, *b as i32, *c as i32);
                    if b == 0 {
                        dynasm!(ops
                            ; .arch x64
                            ; mov rax, QWORD r13 => RunState.top
                            ; sub rax, QWORD r13 => RunState.base
                            ; sub rax, (a + 1)
                            ; mov rsi, rax
                        );
                    } else {
                        dynasm!(ops ; .arch x64 ; mov rsi, (b - 1));
                    }
                    if c == 0 {
                        dynasm!(ops
                            ; .arch x64
                            ; mov rax, QWORD r13 => RunState.top
                            ; sub rax, QWORD r13 => RunState.base
                            ; sub rax, a
                            ; mov rcx, rax
                        );
                    } else if c == 1 {
                        dynasm!(ops ; .arch x64 ; xor ecx, ecx);
                    } else {
                        dynasm!(ops ; .arch x64 ; mov rcx, (c - 1));
                    }
                    dynasm!(ops
                        ; .arch x64
                        ; lea rdi, [r14 + ((a + 1) * 8)] // args ptr = &vals[base + a + 1]
                        ; lea rdx, [r14 + (a * 8)]       // returns ptr = &vals[base + a]
                        ; call extern (*nf as usize)     // direct, statically-known target
                    );
                },
                Residual::Jump(target) => {
                    // If the block ends in a jump, and the block hasn't already been emitted, then
                    // we can elide a jump and instead fallthrough. We will use the target as
                    // `successor`, and so the JIT worklist will compile it immediately after this
                    // code.
                    emit_jump(ops, &alloc, target,
                        off == (block.instructions.len() - 1) && self.jctx.blocks.get(target).is_none());
                    successor = Some(*target);
                },
                Residual::Ret(pc, a, b) => {
                    dynasm!(ops
                        ; .arch x64
                        ; mov rdi, r13 // state
                        ; mov rsi, WORD (*a as i32)
                        ; mov rdx, WORD (*b as i32)
                        ; mov rcx, r14 // base_ptr
                        ; call extern (JitHelper::lua_return as *const () as usize)
                        ; jmp ->exit_jit
                    );
                },
                Residual::Select(targets) => {
                    dynasm!(ops
                        ; mov rax, QWORD r13 => RunState.select
                    );
                    // A taken target's transfer may use rax (`SCRATCH`): the
                    // comparisons only continue on the paths not taken.
                    for (i, target) in targets.iter().enumerate() {
                        dynasm!(ops
                            ; cmp rax, i as i32
                            ; jnz >next_target
                        );
                        emit_jump(ops, &alloc, &target.1, false);
                        dynasm!(ops
                            ; next_target:
                        );
                    }
                    // Should be unreachable, emit a trap
                    dynasm!(ops
                        ; ud2
                    );
                },
                Residual::GC => {
                    dynasm!(ops
                        ; .arch x64
                        ; mov rdi, r12 // owner
                        ; call extern (JitHelper::gc_safepoint as *const () as usize)
                    );
                },
                Residual::ExecWindow(w) => {
                    let stencils = &mut self.jctx.stencils;
                    match plans[&id].ops[off] {
                        Some((skip, want)) => {
                            let mut emits = alloc.reconcile(&want, &**w);
                            emits.extend(alloc.op(&**w, [skip]).expect("a placed op runs at its SKIP"));
                            window_dump!(self.jctx, "      {}", emits_line(&emits));
                            for emit in emits {
                                match emit {
                                    Emit::Op { skip } => {
                                        let body = stencils.body(&**w, skip).expect("a usable skip");
                                        splat(ops, &body, &w.captures(), pool);
                                    }
                                    emit => emit_window_move(ops, emit),
                                }
                            }
                        }
                        // No stencil to copy: call the op's body on the stack.
                        None => {
                            let stores = alloc.flush();
                            window_dump!(self.jctx, "      no stencil: flush {}, then call window_interp", emits_line(&stores));
                            for emit in stores {
                                emit_window_move(ops, emit);
                            }
                            let (op, vtable) = (Rc::as_ptr(w) as *const dyn Window).to_raw_parts();
                            let vtable: *const () = unsafe { core::mem::transmute(vtable) };
                            dynasm!(ops
                                ; .arch x64
                                ; mov rdi, r12 // owner
                                ; mov rsi, r13 // state
                                ; mov rdx, QWORD (op as i64)
                                ; mov rcx, QWORD (vtable as i64)
                                ; call extern (JitHelper::window_interp as *const () as usize)
                            );
                        }
                    }
                },
                Residual::Thunk(_) => {
                    let stores = alloc.stores();
                    window_dump!(self.jctx, "      exit after {}", emits_line(&stores));
                    for emit in stores {
                        emit_window_move(ops, emit);
                    }
                    dynasm!(ops
                        ; mov WORD r13 => RunState.current_off, (off as i16)
                        ; mov rax, QWORD (((-4i32 as u64) << 32 | (id.0 as u64)) as i64)
                        ; mov BYTE r13 => RunState.trap, 1
                        ; jmp ->exit_jit
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
