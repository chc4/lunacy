use crate::generator::{ExecCallback, typeof_};
use qcell::{TCell, TCellOwner};
use crate::vm::{Tc, TcOwner, Vm, RunState, LValue};
use crate::generator::{Block, BlockId, Residual};
use dynasmrt::{ExecutableBuffer, dynasm, DynasmApi, DynasmLabelApi};

use log::debug;
use log::info;
use log::warn;


#[derive(Debug)]
pub struct JitInfo {
    pub buffer: Option<ExecutableBuffer>,
    pub entry: Option<JitExec>
}

impl JitInfo {
    pub fn new() -> Self {
        JitInfo {
            buffer: None,
            entry: None,
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

impl Block {
    pub fn jit_compile(&mut self, id: BlockId) {
        debug!("JIT compiling block {:?}", id);
        let mut ops = dynasmrt::x64::Assembler::new().unwrap();
        let entry = ops.offset();

        // SystemV ABI is RDI, RSI, RDX, RCX, R8, R9
        // JitExec (rust-preserve-none): R12=owner, R13=state, R14=cb_data, R15=cb_vtable

        dynasm!(ops
            ; .arch x64
            ; push rbx
            ; push rbp
            ; push rax // alignment
        );

        let mut insts = std::collections::HashMap::new();
        for (off, res) in self.instructions.iter().enumerate() {
            let label = ops.new_dynamic_label();
            insts.insert(off, label);
        }
        for (off, res) in self.instructions.iter().enumerate() {
            debug!("JIT operation {res:?}");
            let label = insts[&off];
            match res {
                //Residual::Guard { idx, expected } => {
                //    let expected_u8 = *expected as u8;
                //    dynasm!(ops
                //        ; .arch x64
                //        ; =>label
                //        ; mov rdi, r13 // state
                //        ; mov rsi, QWORD (*idx as i64)
                //        ; mov rdx, QWORD (expected_u8 as i64)
                //        ; mov rax, QWORD (JitHelper::check_guard as *const () as i64)
                //        ; call rax
                //        ; test al, al
                //        ; jnz =>insts[&(off + 2)]
                //        // Fail: fallthrough to next (off + 1)
                //    );
                //},
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
                        ; mov rax, QWORD (this_call as i64)
                        ; call rax
                        //// Check for trap
                        ; mov rax, r13 => RunState.trap
                        ; test al, al
                        ; jz >no_trap
                        //// Trap: return (-4, off + 1) so specializer can handle it
                        ; int3
                        ; mov rax, QWORD (((-4i32 as u64) << 32 | (off as u64 + 1)) as i64)
                        ; jmp >exit_jit
                        ; no_trap:
                    );
                },
                Residual::Jump(target) => {
                    let tid = target.0 as i64;
                    dynasm!(ops
                        ; .arch x64
                        ; =>label
                        ; mov rax, QWORD (((tid as u64) << 32) as i64)
                        ; jmp >exit_jit
                    );
                },
                //Residual::EpochCheck { tab, href } => {
                //    let href_u8 = href.0;
                //    dynasm!(ops
                //        ; .arch x64
                //        ; =>label
                //        ; mov rdi, r13 // state
                //        ; mov rsi, r12 // owner
                //        ; mov rdx, QWORD (*tab as i64)
                //        ; mov rcx, QWORD (href_u8 as i64)
                //        ; mov rax, QWORD (JitHelper::check_epoch as *const () as i64)
                //        ; call rax
                //        ; test al, al
                //        ; jz =>insts[&(off + 2)]
                //        // Fail: fallthrough to next (off + 1)
                //    );
                //},
                //Residual::HashGuard { tab, href, expected } => {
                //    let href_u8 = href.0;
                //    let expected_u8 = *expected as u8;
                //    dynasm!(ops
                //        ; .arch x64
                //        ; =>label
                //        ; mov rdi, r13 // state
                //        ; mov rsi, r12 // owner
                //        ; mov rdx, QWORD (*tab as i64)
                //        ; mov rcx, QWORD (href_u8 as i64)
                //        ; mov r8, QWORD (expected_u8 as i64)
                //        ; mov rax, QWORD (JitHelper::check_hash_guard as *const () as i64)
                //        ; call rax
                //        ; test al, al
                //        ; jnz =>insts[&(off + 2)]
                //        // Fail: fallthrough to next (off + 1)
                //    );
                //},
                Residual::Ret(pc, a, b) => {
                    dynasm!(ops
                        ; .arch x64
                        ; =>label
                        ; mov rax, QWORD (((-2i32 as u64) << 32 | (off as u64)) as i64)
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
                _ => {
                    // Fallback to interpreter for other residuals (Thunk)
                    dynasm!(ops
                        ; .arch x64
                        ; =>label
                        ; mov rax, QWORD (((-1i32 as u64) << 32 | (off as u64)) as i64)
                        ; jmp >exit_jit
                    );
                }
            }
        }

        dynasm!(ops
            ; .arch x64
            // Default exit: end of block, return to interpreter at end
            ; mov rax, QWORD (((-1i32 as u64) << 32 | (self.instructions.len() as u64)) as i64)
            ; exit_jit:
            ; pop rdx // padding
            ; pop rbp
            ; pop rbx
            ; ret
        );

        let buf = ops.finalize().unwrap();
        let entrypoint: JitExec = unsafe { core::mem::transmute(buf.ptr(entry)) };

        self.jit_info.buffer = Some(buf);
        self.jit_info.entry = Some(entrypoint);
    }
}
