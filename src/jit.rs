#![allow(unused_parens)]
use std::io::Write;
use std::rc::Rc;
use std::cell::Cell;
use std::collections::{HashMap, BTreeMap};
use crate::{Owner, TLCell, TlcOwner};
use crate::vm::{BlockId, LBoxed, LClosure, LType, LValue, PackedLocation, ReturnLocation, RunState, Tc, Vm};
use crate::gc::{GcInner, GcCtx};
use crate::lboxed::NClosureCell;
use crate::stack::ValueStack;
use crate::generator::{Block, Context, Residual, Specializer, SubPc};
use dynasmrt::{AssemblyOffset, DynamicLabel, DynasmApi, DynasmLabelApi, ExecutableBuffer, dynasm};
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

const JIT_SIZE: usize = 0x1000 * 16;
pub struct JitContext {
    pub memory: std::cell::Cell<dynasmrt::mmap::ExecutableBuffer>,
    pub blocks: HashMap<BlockId, JitPtr, FxBuildHasher>,
    pub pending: BTreeMap<BlockId, DynamicLabel>,
    pub used: usize,
    pub perf_map: Option<std::cell::RefCell<std::fs::File>>,
}

#[derive(Copy, Clone)]
struct JitPtr(*const u8);

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
        Self {
            memory: Cell::new(memory.make_exec().unwrap()),
            blocks: HashMap::default(),
            pending: BTreeMap::new(),
            used: 0,
            perf_map,
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
        // We may have already JIT this block, if it was jumped to by another block
        // first. In that case we just have to jump to it.
        let mut successor = None;
        if let Some(block_ptr) = self.jctx.blocks.get(&id) {
            dynasm!(ops
            ; jmp extern block_ptr.0 as usize
            );
        } else {
            // We need to skip over the uncommitted prologue
            let new_block = JitPtr(unsafe { base.0.add(ops.offset().0) });
            self.jctx.blocks.insert(id, new_block);
            let start_off = ops.offset().0;
            let (_block, entry_succ) = self.jit_block(id, &mut ops, owner);
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
            let successor_pair = successor.and_then(|succ| self.jctx.pending.remove(&succ).map(|label| (succ, label)));
            let Some((pending_block, pending_label)) = successor_pair.or_else(|| self.jctx.pending.pop_first()) else { break };
            debug!("pending block {:?} {:?}", pending_block.0, pending_label);
            let pending_ptr = self.jctx.end();
            let pending_start = ops.offset();
            self.jctx.blocks.insert(pending_block, pending_ptr);
            dynasm!(ops
                ; =>pending_label
            );
            let (_block, next_succ) = self.jit_block(pending_block, &mut ops, owner);
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

    /// JIT compile one block, returning the JIT code offset and optionally the next block to
    /// compile.
    pub fn jit_block(&mut self, id: BlockId, ops: &mut Assembler, owner: &mut Owner) -> (AssemblyOffset, Option<BlockId>) {
        // We try to bias the default exit as the next block to compile. This is only a suggestion,
        // and doesn't affect correctness; `GUARD; JMP failure; RET;` for example may say that
        // `failure` is the "next block" despite not quite being correct.
        let mut successor = None;
        let entry = ops.offset();
        let x = self.jctx.memory.get_mut().as_ptr();
        let block = &self.blocks[id.0];
        let insts: Vec<_> = block.instructions.iter().map(|_| ops.new_dynamic_label()).collect();

        let mut emit_jump = |ops: &mut Assembler, target: &BlockId, skip: bool| {
            if let Some(target_ptr) = self.jctx.blocks.get(target) {
                // We already JIT compiled the block, and can jump to it directly.
                if !skip {
                    dynasm!(ops
                        ; jmp extern target_ptr.0 as usize
                    );
                }
            } else {
                // The block could already be pending from another block in this assembler
                // set. Use it if it already exists, otherwise create a new label for our
                // relocation.
                let pending_label = self.jctx.pending.entry(*target).or_insert_with(|| ops.new_dynamic_label());
                if !skip {
                    dynasm!(ops
                        ; jmp =>*pending_label
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

        for (off, res) in block.instructions.iter().enumerate() {
            debug!("JIT operation {res:?}");
            let label = insts[off];
            dynasm!(ops
                ; => label
            );
            #[cfg(feature = "gas")]
            dynasm!(ops
                ; sub QWORD r13 => RunState.gas, 1
                ; mov WORD r13 => RunState.current_off, (off as i16)
                ; ja >have_gas
                ; mov rax, QWORD (((-1i32 as u64) << 32 | (id.0 as u64)) as i64)
                ; mov BYTE r13 => RunState.trap, 1
                ; jmp ->exit_jit
                ; have_gas:
            );
            loop { match res {
                Residual::Guard { idx, expected } => {
                    // NuN-boxed type check on the 8-byte `LBoxed` slot at `base_ptr[idx]`.
                    // Convention (see generator guard layout): on a *match* we jump to the
                    // success continuation at `off + 2`; a *mismatch* falls through to the
                    // deopt thunk at `off + 1`.
                    //
                    //   * Number   : the value has any `NUMBER_TAG` bit set.
                    //   * Nil/Bool : exact immediate compare (nil = 2, false/true = 6/7).
                    //   * cell types (Table/Closure/String): the value is a raw pointer
                    //     (no `NOT_CELL_MASK` bits) whose offset-0 header byte is the kind.
                    //     We must reject non-cells first so we never dereference a double
                    //     or an immediate.
                    let expected_u8 = *expected as u8;
                    match expected {
                        LType::Number => {
                            dynasm!(ops
                                ; .arch x64
                                ; mov rax, QWORD r14 => LBoxed<'src, 'intern>[*idx as i32]
                                ; mov rcx, QWORD (LBoxed::NUMBER_TAG as i64)
                                ; test rax, rcx
                                ; jnz =>insts[off + 2]
                            );
                        },
                        LType::Nil => {
                            dynasm!(ops
                                ; .arch x64
                                ; cmp QWORD r14 => LBoxed<'src, 'intern>[*idx as i32], (LBoxed::VALUE_NIL as i32)
                                ; jz =>insts[off + 2]
                            );
                        },
                        LType::Bool => {
                            dynasm!(ops
                                ; .arch x64
                                ; mov rax, QWORD r14 => LBoxed<'src, 'intern>[*idx as i32]
                                ; or rax, 1 // false(6) -> 7, true(7) -> 7
                                ; cmp rax, (LBoxed::VALUE_TRUE as i32)
                                ; jz =>insts[off + 2]
                            );
                        },
                        LType::Table => {
                            dynasm!(ops
                                ; .arch x64
                                ; mov rax, QWORD r14 => LBoxed<'src, 'intern>[*idx as i32]
                                ; mov rcx, QWORD (LBoxed::NOT_CELL_MASK as i64)
                                ; test rax, rcx
                                ; jnz >guard_fail // not a cell
                                ; cmp BYTE [rax], (LBoxed::KIND_TABLE as i8)
                                ; jz =>insts[off + 2]
                                ; guard_fail:
                            );
                        },
                        LType::Closure => {
                            dynasm!(ops
                                ; .arch x64
                                ; mov rax, QWORD r14 => LBoxed<'src, 'intern>[*idx as i32]
                                ; mov rcx, QWORD (LBoxed::NOT_CELL_MASK as i64)
                                ; test rax, rcx
                                ; jnz >guard_fail // not a cell
                                ; movzx ecx, BYTE [rax]
                                ; sub ecx, (LBoxed::KIND_LCLOSURE as i32) // LClosure(2)/NClosure(3)
                                ; cmp ecx, 1
                                ; jbe =>insts[off + 2]
                                ; guard_fail:
                            );
                        },
                        LType::String => {
                            dynasm!(ops
                                ; .arch x64
                                ; mov rax, QWORD r14 => LBoxed<'src, 'intern>[*idx as i32]
                                ; mov rcx, QWORD (LBoxed::NOT_CELL_MASK as i64)
                                ; test rax, rcx
                                ; jnz >guard_fail // not a cell
                                ; movzx ecx, BYTE [rax]
                                ; sub ecx, (LBoxed::KIND_OWNED as i32) // Owned(4)/Interned(5)
                                ; cmp ecx, 1
                                ; jbe =>insts[off + 2]
                                ; guard_fail:
                            );
                        },
                        _ => {
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
                    }
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
                    // TODO: For now look up if there is a JIT block for the entrypoint with no known types
                    let next_stack = unsafe { (*lclos.ro(owner).prototype).max_stack.into() };
                    let types = vec![LType::Unknown; next_stack];
                    let ctx = Rc::new(Context::new(types));
                    let versions = self.versions.get(&lclos.ro(owner).prototype).unwrap();
                    let entry: Option<*const ()> = if let Some(block) = versions.get(&(SubPc::new(0), ctx.clone())) {
                        self.blocks[block.0].jit_info.entry.map(|f| f as *const _)
                    } else {
                        // This shouldn't ever happen...?
                        None
                    };
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
                        Some(_) | None => {
                            // TODO: Even though we don't have the block it's unavailable now, we
                            // could emit a patchpoint and fill it in once we emit it. For now, we
                            // just bailout to the interpreter forever because we missed our
                            // opportunity.
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
                    emit_jump(ops, target,
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
                    for (i, target) in targets.iter().enumerate() {
                        dynasm!(ops
                            ; cmp rax, i as i32
                            ; jnz >next_target
                        );
                        emit_jump(ops, &target.1, false);
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
                Residual::Thunk(_) => {
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
        }

        (entry, successor)
    }
}

