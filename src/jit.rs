use std::cell::Cell;
use std::collections::{HashMap, BTreeMap};
use qcell::{TCell, TCellOwner};
use crate::vm::{Tc, TcOwner, Vm, RunState, LValue};
use crate::generator::{Specializer, Block, BlockId, Residual};
use dynasmrt::{AssemblyOffset, DynamicLabel, DynasmApi, DynasmLabelApi, ExecutableBuffer, dynasm};
use rustc_hash::FxBuildHasher;

use log::debug;
use log::info;
use log::warn;

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

pub type JitExec = for<'a, 'src, 'intern> extern "rust-preserve-none" fn(&mut TCellOwner<TcOwner>, &'a mut RunState<'src, 'intern>) -> u64;

pub fn get_ptr_from_closure(f: &dyn for <'a, 'b, 'src, 'intern> Fn(&mut TCellOwner<TcOwner>, &'b mut RunState<'src, 'intern>)) -> (*const (), usize, usize) {
    let (addr, meta) = (f as *const dyn for <'a, 'b, 'src, 'intern> Fn(&mut TCellOwner<TcOwner>, &'b mut RunState<'src, 'intern>)).to_raw_parts();
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
            (val.typeof_() as u8) == expected
        }
    }
    pub unsafe extern "C" fn check_epoch(state: *mut (), tab: usize, href: u8) -> bool {
        unsafe {
            //println!("state {:?} {} {}", state, tab, href);
            let state = state as *mut RunState;
            // Forge an owner
            let mut owner = ();
            let owner = (&raw mut owner as *mut TCellOwner<TcOwner>).as_ref_unchecked();
            let rs = &*state;
            let hwit = rs.hash_witnesses[rs.witness_base + href as usize].as_ref().unwrap();
            let tab_val = &rs.vals[rs.base + tab];
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
            let owner = (&raw mut owner as *mut TCellOwner<TcOwner>).as_ref_unchecked();
            let rs = &*state;
            let hwit = rs.hash_witnesses[rs.witness_base + href as usize].as_ref().unwrap();
            let tab_val = &rs.vals[rs.base + tab];
            let LValue::Table(tab) = tab_val else { unreachable!() };
            let Some((key, val)) = tab.ro(owner).hash.get_index(hwit.index) else { unreachable!() };
            (val.typeof_() as u8) == expected
        }
    }
}

const JIT_SIZE: usize = 0x1000 * 16;
pub struct JitContext {
    pub memory: std::cell::Cell<dynasmrt::mmap::ExecutableBuffer>,
    pub blocks: HashMap<BlockId, JitPtr, FxBuildHasher>,
    pub pending: BTreeMap<BlockId, DynamicLabel>,
    pub used: usize,
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
        Self {
            memory: Cell::new(memory.make_exec().unwrap()),
            blocks: HashMap::default(),
            pending: BTreeMap::new(),
            used: 0,
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
    pub fn jit_compile(&mut self, id: BlockId) {
        debug!("JIT compiling block {:?}", id);
        let base = self.jctx.end();
        let mut ops = dynasmrt::VecAssembler::<dynasmrt::x64::X64Relocation>::new(base.0 as usize);
        let entry = ops.offset();

        // SystemV ABI is RDI, RSI, RDX, RCX, R8, R9
        // JitExec (rust-preserve-none): R12=owner, R13=state

        dynasm!(ops
            ; .arch x64
            ; push rbx
            ; push rbp
            ; push rax // alignment
        );
        // TODO: Pin state.vals.as_ptr() to a register, which will let us remove a lot of the
        // JitHelper function calls.

        // We may have already JIT this block, if it was jumped to by another block
        // first. In that case we just have to jump to it.
        if let Some(block_ptr) = self.jctx.blocks.get(&id) {
            dynasm!(ops
            ; jmp extern block_ptr.0 as usize
            );
        } else {
            // We need to skip over the uncommitted prologue
            let new_block = JitPtr(unsafe { base.0.add(ops.offset().0) });
            self.jctx.blocks.insert(id, new_block);
            let _block = self.blocks[id.0 as usize].jit_body(id, &mut self.jctx, &mut ops);
        }


        // Reserve the full length of our compiled function
        let end = ops.offset();
        self.jctx.reserve(end.0);

        // Now we need to go through and also compile all of the pending labels for other blocks.
        while let Some((pending_block, pending_label)) = self.jctx.pending.pop_first() {
            debug!("pending block {:?} {:?}", pending_block.0, pending_label);
            let pending_ptr = self.jctx.end();
            let pending_start = ops.offset();
            self.jctx.blocks.insert(pending_block, pending_ptr);
            dynasm!(ops
                ; =>pending_label
            );
            let _block = self.blocks[pending_block.0 as usize].jit_body(pending_block, &mut self.jctx, &mut ops);
            self.jctx.reserve(ops.offset().0 - pending_start.0);
        }

        debug!("drained pending");
        let buf = ops.finalize().unwrap();
        let Some(slab) = self.jctx.commit(base, buf.as_slice()) else { panic!() };
        let entrypoint: JitExec = unsafe { core::mem::transmute(slab.add(entry.0)) };

        self.blocks[id.0 as usize].jit_info.entry = Some(entrypoint);
    }
}

type Assembler = dynasmrt::VecAssembler::<dynasmrt::x64::X64Relocation>;
impl Block {
    pub fn jit_body(&mut self, id: BlockId, jctx: &mut JitContext, ops: &mut Assembler) -> AssemblyOffset {
        let entry = ops.offset();
        let x = jctx.memory.get_mut().as_ptr();
        let insts: Vec<_> = self.instructions.iter().map(|_| ops.new_dynamic_label()).collect();

        let mut emit_jump = |ops: &mut Assembler, target: &BlockId| {
            if let Some(target_ptr) = jctx.blocks.get(target) {
                // We already JIT compiled the block, and can jump to it directly.
                dynasm!(ops
                    ; jmp extern target_ptr.0 as usize
                );
            } else {
                // The block could already be pending from another block in this assembler
                // set. Use it if it already exists, otherwise create a new label for our
                // relocation.
                let pending_label = jctx.pending.entry(*target).or_insert_with(|| ops.new_dynamic_label());
                dynasm!(ops
                    ; jmp =>*pending_label
                );
            }
        };

        for (off, res) in self.instructions.iter().enumerate() {
            debug!("JIT operation {res:?}");
            let label = insts[off];
            dynasm!(ops
                ; => label
            );
            #[cfg(feature = "gas")]
            dynasm!(ops
                ; sub QWORD r13 => RunState.gas, 1
                ; mov WORD r13 => RunState.current_off, (off as i16)
                ; mov rax, QWORD (((-1i32 as u64) << 32 | (id.0 as u64)) as i64)
                ; jbe >exit_jit
            );
            match res {
                Residual::Guard { idx, expected } => {
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
                    let (this_obj, this_vtable, this_call) = get_ptr_from_closure(f.1.as_ref());
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
                        ; jmp >exit_jit
                        ; no_trap:
                    );
                },
                //Residual::NativeCall { nf, a, b, c } => {
                //    // NativeFunction is an extern "rust-call" like Exec.
                //    dynasm!(ops
                //        ; mov rsi, r12 // owner
                //        ; mov rdx, r13 // state
                //        // Lua wants to see PC+1, and also we want to resume to PC+1 if we trap.
                //        ; mov WORD r13 => RunState.current_off, ((off + 1) as i16)

                //        ; call extern (*nf as usize)
                //    );
                //},
                Residual::Jump(target) => {
                    emit_jump(ops, target);
                },
                Residual::Ret(pc, a, b) => {
                    dynasm!(ops
                        ; .arch x64
                        ; mov WORD r13 => RunState.current_off, (off as i16)
                        ; mov rax, QWORD (((-2i32 as u64) << 32 | (id.0 as u64)) as i64)
                        ; jmp >exit_jit
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
                        emit_jump(ops, &target.1);
                        dynasm!(ops
                            ; next_target:
                        );
                    }
                    // Should be unreachable, emit a trap
                    dynasm!(ops
                        ; int3
                    );
                },
                Residual::Thunk(_) => {
                    dynasm!(ops
                        ; mov WORD r13 => RunState.current_off, (off as i16)
                        ; mov rax, QWORD (((-4i32 as u64) << 32 | (id.0 as u64)) as i64)
                        ; jmp >exit_jit
                    );
                },
                _ => {
                    if off == 0 {
                        // If we're trying to bailout from the first instruction, we
                        // need to record it as a JIT exit so that we don't try to call
                        //
                        // this same function again immediately in a loop.
                        dynasm!(ops
                            ; .arch x64
                            ; mov WORD r13 => RunState.current_off, (off as i16)
                            ; mov rax, QWORD (((-1i32 as u64) << 32 | (id.0 as u64)) as i64)
                            ; jmp >exit_jit
                        );
                    } else {
                        // Fallback to interpreter for other residuals
                        dynasm!(ops
                            ; .arch x64
                            ; mov rax, QWORD (((off as u64) << 32 | (id.0 as u64)) as i64)
                            ; jmp >exit_jit
                        );
                    }
                }
            }
        }

        dynasm!(ops
            ; .arch x64
            // Default exit: end of block, return to interpreter at end
            ; int3
            ; mov rax, QWORD (((self.instructions.len() as u64) << 32 | (id.0 as u64)) as i64)
            ; exit_jit:
            ; pop rdx // padding
            ; pop rbp
            ; pop rbx
            ; ret
        );
        entry
    }
}
