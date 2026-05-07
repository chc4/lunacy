#![allow(unused)]
#![feature(trait_alias, ptr_metadata, fn_traits, rust_preserve_none_cc)]
use dynasmrt::ExecutableBuffer;
use qcell::{TCell, TCellOwner};
use std::rc::Rc;
use std::ops::Deref;
use std::marker::PhantomData;
use std::num::Wrapping;

use dynasmrt::{dynasm, DynasmApi, DynasmLabelApi};
use log::{info, debug};

pub struct TcOwner;
//type ExecCallback<'a, 'src, 'intern> = &'a mut dyn for<'b> FnMut(ExecEffect, &mut TCellOwner<TcOwner>, &'b mut RunState<'src, 'intern>);
pub type ExecCallback<'a, 'src, 'intern> = &'a mut dyn for<'b> FnMut(());
trait ExecFn = for <'a, 'b, 'src, 'intern> Fn(&mut TCellOwner<TcOwner>, &'b mut RunState<'src, 'intern>, ExecCallback<'a, 'src, 'intern>) + Sync + 'static;
#[derive(Clone)]
pub struct ResidualExec(&'static str, Rc<dyn ExecFn>);

type JitExec = for<'a, 'src, 'intern> extern "rust-preserve-none" fn(&mut TCellOwner<TcOwner>, &'a mut RunState<'src, 'intern>, ExecCallback<'a, 'src, 'intern>);

pub struct RunState<'src, 'intern> {
    acc: std::num::Wrapping<usize>,
    thing: TCell<TcOwner, usize>,
    _phantom: PhantomData<(&'src (), &'intern ())>,
}

struct Jit {
    program: Vec<ResidualExec>,
}

use core::ptr::*;
use core::ptr::DynMetadata;
use core::mem;
use core::ptr;
pub fn get_ptr_from_closure(f: &dyn ExecFn) -> (*const (), usize, usize) {
    let fn_call = <&dyn ExecFn>::call;
    let (addr, meta) = (f as *const dyn ExecFn).to_raw_parts();
    #[derive(Debug)]
    #[repr(C)]
    struct RawMeta {
        vtable: &'static [usize;5]
    }
    debug!("{addr:?}, {meta:?}");
    unsafe {
        let vtable = mem::transmute::<_, RawMeta>(meta);
        println!("{addr:?} {vtable:x?}");
        // Why is it at 5? Who knows.
        let call = vtable.vtable[4];
        println!("closure body: {:x}", call);
        return (addr, vtable.vtable as &_ as *const _ as usize, call);
    }
}

impl Jit {
    fn new(program: Vec<ResidualExec>) -> Self {
        Self {
            program,
        }
    }

    fn jit(&mut self) -> (ExecutableBuffer, JitExec) {
        let mut ops = dynasmrt::x64::Assembler::new().unwrap();
        ops.local_label("entry");

        // SystemV ABI is RDI, RSI, RDX
        // Rust ABI may clobber those, however, so we save+restore them through Rust
        // preserved registers (R11, R12).
        //
        // For the closure , RDX = RunState

        dynasm!(ops
            ; .arch x64
        );


        let entry = ops.offset();
        dbg!(entry);
        dynasm!(ops
            ; .arch x64
            ; ->entry:
            ; push rax
        );

        for entry in &self.program {
            let (this_obj, this_vtable, this_call) = get_ptr_from_closure(entry.1.deref());
            // TODO: we could instead mmap a buffer close to our closures, and then guarantee a
            // 32bit displacement can address them. This would both free up rbx as a GPR and remove
            // the dispatch through a register.
            dynasm!(ops
                ; .arch x64
                ; mov rsi, r12
                ; mov rdx, r13
                ; mov rcx, r14
                ; mov r8, r15
                ; mov rax, QWORD (this_vtable as i64)
                ; mov rdi, QWORD (this_obj as i64)
                ; mov rbx, QWORD (this_call as i64)
                ; call rbx
            );
        }

        dynasm!(ops
            ; .arch x64
            ; pop rax
            ; ret
        );

        let buf = ops.finalize().unwrap();

        let entrypoint: JitExec = unsafe { core::mem::transmute(buf.ptr(entry)) };
        println!("{entrypoint:?}");

        (buf, entrypoint)
    }

    fn interpreter<'a, 'intern, 'src>(&self, owner: &mut TCellOwner<TcOwner>, state: &'a mut RunState<'src, 'intern>, cb: ExecCallback<'a, 'src, 'intern>) {
        for op in &self.program {
            (op.1)(owner, state, cb);
        }
    }
}

fn main() {
    env_logger::builder().format_timestamp(None).format_source_path(true).init();

    let mut capture = core::hint::black_box(0x1abbccdd);
    let mut program = Jit::new(vec![
        ResidualExec("one", Rc::new(|owner, state, cb| {
            state.acc = Wrapping(1);
        })),
        ResidualExec("inc", Rc::new(|owner, state, cb| {
            state.acc += 1;
            println!("blah");
        })),
        ResidualExec("move", Rc::new(|owner, state, cb| {
            *state.thing.rw(owner) = state.acc.0;
        })),
        ResidualExec("cb", Rc::new(|owner, state, cb| {
            cb(());
        })),
        ResidualExec("capture", Rc::new(move |owner, state, cb| {
            state.acc = Wrapping(capture);
        })),
    ]);

    // Create a function that calls closures for us to copy the ABI shuffling from.
    // We can't use it as a real copy&patch template with relocations because we only
    // want to use the prologue and epilogue once, with N calls in the middle.
    struct MockOwner;
    static MOCK_RESIDUAL: TCell<MockOwner, &dyn ExecFn> = TCell::new(&|owner, state, cb| { println!("mock"); });
    extern "rust-preserve-none" fn safe_call<'a, 'src, 'intern>(owner: &mut TCellOwner<TcOwner>, state: &'a mut RunState<'src, 'intern>, cb: ExecCallback<'a, 'src, 'intern>)
    {
        let mowner = TCellOwner::new();
        let binding = &MOCK_RESIDUAL;
        let res = binding.ro(&mowner);
        (res)(owner, state, cb);
        (res)(owner, state, cb);
        return (res)(owner, state, cb)
    }
    let mut mowner = TCellOwner::new();
    *MOCK_RESIDUAL.rw(&mut mowner) = &|owner, state, cb| { cb(()) };
    println!("safe_call @ {:x}", safe_call as usize);
    drop(mowner);

    let (buf, entry) = program.jit();
    let mut owner = TCellOwner::new();
    let mut state = RunState {
        acc: Wrapping(0),
        thing: TCell::new(0),
        _phantom: PhantomData
    };
    safe_call(&mut owner, &mut state, &mut |()| { println!("mock cb"); });
    let jit_start = std::time::Instant::now();
    for i in 0..10000 {
        entry(&mut owner, &mut state, &mut |()| { println!("yippee {i}"); });
    }
    let jit_finish = state.acc;
    let jit_elapsed = jit_start.elapsed();
    let start = std::time::Instant::now();
    for i in 0..10000 {
        program.interpreter(&mut owner, &mut state, &mut |()| { println!("yippee {i}"); });
    }
    let elapsed = start.elapsed();
    println!("interpreter {:x?} took {:?}", state.acc, elapsed);
    println!("jit {:x?} took {:?}", jit_finish, jit_elapsed);

}
