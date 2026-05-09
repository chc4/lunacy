use std::cell::Cell;
use std::collections::{HashMap, BTreeMap};
use crate::generator::{ExecCallback, typeof_};
use qcell::{TCell, TCellOwner};
use crate::vm::{Tc, TcOwner, Vm, RunState, LValue};
use crate::generator::{Specializer, Block, BlockId, Residual};
use dynasmrt::{AssemblyOffset, DynamicLabel, DynasmApi, DynasmLabelApi, ExecutableBuffer, dynasm};

use log::debug;
use log::info;
use log::warn;

#[cfg(feature = "immediate_jit")]
const INITIAL_HOTNESS: usize = 0;
#[cfg(not(feature = "immediate_jit"))]
const INITIAL_HOTNESS: usize = 200;

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

pub type JitExec = for<'a, 'src, 'intern> extern "rust-preserve-none" fn(&mut TCellOwner<TcOwner>, &'a mut RunState<'src, 'intern>, ExecCallback<'a, 'src, 'intern>) -> u64;

pub fn get_ptr_from_closure(f: &dyn for <'a, 'b, 'src, 'intern> Fn(&mut TCellOwner<TcOwner>, &'b mut RunState<'src, 'intern>, ExecCallback<'a, 'src, 'intern>)) -> (*const (), usize, usize) {
    let (addr, meta) = (f as *const dyn for <'a, 'b, 'src, 'intern> Fn(&mut TCellOwner<TcOwner>, &'b mut RunState<'src, 'intern>, ExecCallback<'a, 'src, 'intern>)).to_raw_parts();
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
            let state = state as *mut RunState;
            let rs = &*state;
            let val = &rs.vals[rs.base + idx];
            (typeof_(val) as u8) == expected
        }
    }
    pub unsafe extern "C" fn check_epoch(state: *mut (), owner: *mut (), tab: usize, href: u8) -> bool {
        unsafe {
            let state = state as *mut RunState;
            let owner = owner as *mut TCellOwner<TcOwner>;
            let rs = &*state;
            let owner = &*owner;
            let hwit = rs.hash_witnesses[rs.witness_base + href as usize].as_ref().unwrap();
            let tab_val = &rs.vals[rs.base + tab];
            let LValue::Table(tab) = tab_val else { return false };
            debug!("JIT check_epoch sees {} == {}", hwit.epoch, tab.ro(owner).epoch);
            hwit.epoch != tab.ro(owner).epoch
        }
    }
    pub unsafe extern "C" fn check_hash_guard(state: *mut (), owner: *mut (), tab: usize, href: u8, expected: u8) -> bool {
        unsafe {
            let state = state as *mut RunState;
            let owner = owner as *mut TCellOwner<TcOwner>;
            let rs = &*state;
            let owner = &*owner;
            let hwit = rs.hash_witnesses[rs.witness_base + href as usize].as_ref().unwrap();
            let tab_val = &rs.vals[rs.base + tab];
            let LValue::Table(tab) = tab_val else { return false };
            let Some((key, val)) = tab.ro(owner).hash.get_index(hwit.index) else { return false };
            (typeof_(val) as u8) == expected
        }
    }
}

const JIT_SIZE: usize = 0x1000 * 16;
pub struct JitContext {
    pub memory: std::cell::Cell<dynasmrt::mmap::ExecutableBuffer>,
    pub blocks: HashMap<BlockId, JitPtr>,
    pub pending: BTreeMap<BlockId, DynamicLabel>,
    pub used: usize,
}

#[derive(Copy, Clone)]
struct JitPtr(*const u8);

impl JitContext {
    pub fn new() -> Self {
        let mut memory = dynasmrt::mmap::MutableBuffer::new(JIT_SIZE).unwrap();
        // Set the JIT memory to the max size initially, so that we don't need to
        // mprotect back to mutable just to reserve
        memory.set_len(JIT_SIZE);
        Self {
            memory: Cell::new(memory.make_exec().unwrap()),
            blocks: HashMap::new(),
            pending: BTreeMap::new(),
            used: 0
        }
    }

    fn end(&self) -> JitPtr {
        let mut buf = self.memory.take();
        let ptr = JitPtr(unsafe { buf.as_ptr().add(self.used).cast() });
        self.memory.set(buf);
        ptr
    }

    // Reserve memory in the JIT buffer
    fn reserve(&mut self, len: usize) {
        assert!(self.used + len < JIT_SIZE);
        self.used += len;
    }

    // Commit contents 
    fn commit(&mut self, ptr: JitPtr, contents: &[u8]) -> Option<*mut u8> {
        let mut mutable = self.memory.take().make_mut().unwrap();
        assert!(ptr.0 >= mutable.as_mut_ptr());
        assert!(ptr.0 <= unsafe { mutable.as_mut_ptr().add(self.used) });
        assert!(unsafe { ptr.0.add(contents.len()) } <= unsafe { mutable.as_mut_ptr().add(self.used) });
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
        // JitExec (rust-preserve-none): R12=owner, R13=state, R14=cb_data, R15=cb_vtable

        dynasm!(ops
            ; .arch x64
            ; push rbx
            ; push rbp
            ; push rax // alignment
        );

        // We may have already JIT this block, if it was jumped to by another block
        // first. In that case we just have to jump to it.
        if let Some(block_ptr) = self.jctx.blocks.get(&id) {
            dynasm!(ops
            ; jmp extern block_ptr.0 as usize
            );
        } else {
            self.jctx.blocks.insert(id, base);
            let _block = self.blocks[id.0].jit_body(id, &mut self.jctx, &mut ops);
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
            let _block = self.blocks[pending_block.0].jit_body(pending_block, &mut self.jctx, &mut ops);
            self.jctx.reserve(ops.offset().0 - pending_start.0);
        }

        debug!("drained pending");
        let buf = ops.finalize().unwrap();
        let Some(slab) = self.jctx.commit(base, buf.as_slice()) else { panic!() };
        let entrypoint: JitExec = unsafe { core::mem::transmute(slab.add(entry.0)) };

        self.blocks[id.0].jit_info.entry = Some(entrypoint);
    }
}

impl Drop for JitContext {
    fn drop(&mut self) {
        // SAFETY: This requires that no JIT code is currently running, all JitInfo for Blocks
        // that were derived from our memory have been destroyed.
        // Under normal circumstances this is upheld by storing the JitContext inside the
        // Specializer that will use it for Blocks.
    }
}
type Assembler = dynasmrt::VecAssembler::<dynasmrt::x64::X64Relocation>;
impl Block {
    pub fn jit_body(&mut self, id: BlockId, jctx: &mut JitContext, ops: &mut Assembler) -> AssemblyOffset {
        let entry = ops.offset();
        let mut insts = std::collections::HashMap::new();
        for (off, res) in self.instructions.iter().enumerate() {
            let label = ops.new_dynamic_label();
            insts.insert(off, label);
        }
        for (off, res) in self.instructions.iter().enumerate() {
            debug!("JIT operation {res:?}");
            let label = insts[&off];
            match res {
                Residual::Guard { idx, expected } => {
                    let expected_u8 = *expected as u8;
                    dynasm!(ops
                        ; .arch x64
                        ; =>label
                        ; mov rdi, r13 // state
                        ; mov rsi, QWORD (*idx as i64)
                        ; mov rdx, QWORD (expected_u8 as i64)
                        ; mov rax, QWORD (JitHelper::check_guard as *const () as i64)
                        ; call rax
                        ; test al, al
                        ; jnz =>insts[&(off + 2)]
                        // Fail: fallthrough to next (off + 1)
                    );
                },
                Residual::EpochCheck { tab, href } => {
                    let href_u8 = href.0;
                    dynasm!(ops
                        ; .arch x64
                        ; =>label
                        ; mov rsi, r12 // owner
                        ; mov rdi, r13 // state
                        ; mov rdx, QWORD (*tab as i64)
                        ; mov rcx, QWORD (href_u8 as i64)
                        ; mov rax, QWORD (JitHelper::check_epoch as *const () as i64)
                        ; call rax
                        ; test al, al
                        ; jz =>insts[&(off + 2)]
                        // Fail: fallthrough to next (off + 1)
                    );
                },
                Residual::HashGuard { tab, href, expected } => {
                    let href_u8 = href.0;
                    let expected_u8 = *expected as u8;
                    dynasm!(ops
                        ; .arch x64
                        ; =>label
                        ; mov rsi, r12 // owner
                        ; mov rdi, r13 // state
                        ; mov rdx, QWORD (*tab as i64)
                        ; mov rcx, QWORD (href_u8 as i64)
                        ; mov r8, QWORD (expected_u8 as i64)
                        ; mov rax, QWORD (JitHelper::check_hash_guard as *const () as i64)
                        ; call rax
                        ; test al, al
                        ; jnz =>insts[&(off + 2)]
                        // Fail: fallthrough to next (off + 1)
                    );
                },
                Residual::Exec(f) => {
                    let (this_obj, this_vtable, this_call) = get_ptr_from_closure(f.1.as_ref());
                    dynasm!(ops
                        ; .arch x64
                        ; =>label
                        ; mov rsi, r12 // owner
                        ; mov rdx, r13 // state
                        ; mov rcx, r14 // cb data
                        ; mov r8, r15  // cb vtable
                        ; mov rdi, QWORD (this_obj as i64)
                        //; mov rax, QWORD (this_vtable as i64)
                        ; mov rbx, QWORD (this_call as i64)
                        // Lua wants to see PC+1, and also we want to resume to PC+1 if we trap.
                        ; mov WORD r13 => RunState.current_off, ((off + 1) as i16)
                        ; call rbx
                        //// Check for trap
                        ; mov rax, r13 => RunState.trap
                        ; test al, al
                        ; jz >no_trap
                        //// Trap 4 so specializer can handle it
                        ; mov rax, QWORD (((-1i32 as u64) << 32 | (id.0 as u64)) as i64)
                        ; jmp >exit_jit
                        ; no_trap:
                    );
                },
                Residual::Jump(target) => {
                    if let Some(target_ptr) = jctx.blocks.get(target) {
                        // We already JIT compiled the block, and can jump to it directly.
                        dynasm!(ops
                            ; =>label
                            ; jmp extern target_ptr.0 as usize
                        );
                    } else {
                        // The block could already be pending from another block in this assembler
                        // set. Use it if it already exists, otherwise create a new label for our
                        // relocation.
                        let pending_label = jctx.pending.entry(*target).or_insert_with(|| ops.new_dynamic_label());
                        dynasm!(ops
                            ; =>label
                            ; jmp =>*pending_label
                        );
                    }
                },
                Residual::Ret(pc, a, b) => {
                    dynasm!(ops
                        ; .arch x64
                        ; =>label
                        ; mov WORD r13 => RunState.current_off, (off as i16)
                        ; mov rax, QWORD (((-2i32 as u64) << 32 | (id.0 as u64)) as i64)
                        ; jmp >exit_jit
                    );
                },
                //Residual::Select(targets) => {
                //    dynasm!(ops
                //        ; .arch x64
                //        ; =>label
                //        ; mov rax, QWORD (((-3i32 as u64) << 32 | (off as u64)) as i64)
                //        ; jmp >exit_jit
                //    );
                //},
                Residual::Thunk(_) => {
                    dynasm!(ops
                        ; mov WORD r13 => RunState.current_off, (off as i16)
                        ; mov rax, QWORD (((-4i32 as u64) << 32 | (id.0 as u64)) as i64)
                        ; jmp >exit_jit
                    );
                },
                _ => {
                    // Fallback to interpreter for other residuals
                    dynasm!(ops
                        ; .arch x64
                        ; =>label
                        ; mov rax, QWORD (((off as u64) << 32 | (id.0 as u64)) as i64)
                        ; jmp >exit_jit
                    );
                }
            }
        }

        dynasm!(ops
            ; .arch x64
            // Default exit: end of block, return to interpreter at end
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
