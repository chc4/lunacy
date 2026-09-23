//! Copy&patch register-window ops. See `docs/jit-register-cache.md` and the
//! `src/bin/windowed.rs` proof of concept this is ported from.
//!
//! The mechanism is op-agnostic: any emit site declares its own window op with
//! [`windowed!`], exactly as it would a `define_exec!` closure. That produces:
//!
//! * a struct whose fields are the op's **captures** (its holes' values) plus the
//!   stack slots each window operand is loaded from / flushed to, and which
//!   implements [`Window`] — a trait object the specializer stores in
//!   `Residual::ExecWindow`, so no processing site enumerates ops (like `Exec`'s
//!   closure);
//! * an `#[inline(always)]` body shared by both tiers (single source of truth);
//! * a `rust-preserve-none` stencil `__stencil::<K>`: the fixed params
//!   `(owner, state, base)` (the ABI the JIT pins in r12/r13/r14) followed by the
//!   register window as **scalar** `LBoxed` params `w0..w3` (r15, rdi, rsi, rdx).
//!   Scalars, not `[LBoxed; N]` — Rust passes arrays by pointer whatever the ABI,
//!   which would put the window in memory. `K` is the window shift: the op's
//!   operands are `w[K..K+ARITY]`. The stencil ends in `become` to the op's own
//!   continuation, which the copier slices off so the window falls through into
//!   the next stencil.
//!
//! Captures reach the stencil through `extern_weak` hole statics (`__lunacy_holeN`).
//! Under plain PIE each read is a RIP-relative load from the hole's GOT slot; the
//! copier finds those loads via this executable's own dynamic relocations (goblin)
//! and repoints them at a shared value pool laid after the code. The interpreter
//! tier cannot run the stencil itself (its holes read 0 until patched), so it runs
//! the same body with captures from the struct: load the operand slots, run,
//! flush.
//!
//! Copying a stencil (`stencil_body`) decodes it (yaxpeax-x86). A well-formed
//! stencil's last instruction is its `become`: a tail jump to the op's
//! continuation, sliced off so the next stencil falls through. Every other
//! RIP-relative reference in the body is reported so it can be re-targeted
//! wherever the body lands: hole loads (repointed at the op's capture values),
//! other continuation references (at the copy's fall-through point), and
//! everything else — calls out of line (e.g. into `IndexMap`), GOT slots,
//! rodata — at its original absolute address, which stays in rel32 range because
//! JIT memory is mapped within ±2GiB of the binary. In the JIT these all become
//! dynasm relocations patched at `finalize`; `assemble` does the same by hand.
//! Calls are fine anywhere (they return), but a jump that leaves the stencil
//! without being a `become` would skip the rest of the chain, so it is rejected
//! loudly: a sibling tail call, or an indirect jump such as a jump table (whose
//! entries lead back into the original function). An opt-level 0 build of
//! `NumericIntInt` hits the latter (`match OP` isn't folded); optimized builds
//! don't. The interpreter tier runs any window op regardless.

use std::collections::HashMap;

use dynasmrt::mmap::{ExecutableBuffer, MutableBuffer};
use smallvec::SmallVec;

use crate::lboxed::LBoxed;
use crate::vm::RunState;
use crate::Owner;

/// Number of register-window slots (w0..w3 = r15, rdi, rsi, rdx).
pub const WINDOW: usize = 4;
/// Number of hole statics available to captures.
pub const MAX_HOLES: usize = 2;
/// A window op's hole values. (Literal length: with `generic_const_exprs` on, a
/// named const in a trait method signature would make `Window` dyn-incompatible.)
pub type Captures = SmallVec<[u64; 2]>;

// ---- holes / continuation / anchor ---------------------------------------

unsafe extern "C" {
    #[linkage = "extern_weak"]
    static __lunacy_hole0: *const ();
    #[linkage = "extern_weak"]
    static __lunacy_hole1: *const ();
    /// Deliberately never defined, and *not* weak: it is only referenced by a
    /// window op that declares more captures than there are holes
    /// (`MAX_HOLES`), so that mistake fails loudly at link time.
    static unresolved_window_hole__too_many_captures: *const ();
}

/// Read hole `I`. The index is a const generic, so monomorphization picks the
/// arm: a stencil only references the hole statics it actually uses, and only an
/// over-captured op references the unresolved symbol (even in debug builds).
#[doc(hidden)]
#[inline(always)]
pub unsafe fn hole<const I: usize>() -> u64 {
    unsafe {
        match I {
            0 => __lunacy_hole0 as u64,
            1 => __lunacy_hole1 as u64,
            _ => unresolved_window_hole__too_many_captures as u64,
        }
    }
}

/// Stable symbol for recovering the PIE load bias (runtime address vs ELF vaddr).
#[unsafe(no_mangle)]
pub extern "C" fn __lunacy_window_anchor() {}

// ---- captures -------------------------------------------------------------

/// A value that can live in a hole: any `Copy` type of at most 8 bytes, with no
/// borrowed lifetimes (window structs are `'static`). It travels as its raw bits.
pub trait Capture: Copy + std::fmt::Debug + 'static {
    fn to_bits(self) -> u64;
    unsafe fn from_bits(bits: u64) -> Self;
}

/// Monomorphization-time check that a capture fits in a hole. (An associated
/// const, since `generic_const_exprs` rejects inline `const { assert!(..) }`.)
struct FitsInHole<T>(core::marker::PhantomData<T>);
impl<T> FitsInHole<T> {
    const OK: () = assert!(core::mem::size_of::<T>() <= 8, "captures must fit in 8 bytes");
}

impl<T: Copy + std::fmt::Debug + 'static> Capture for T {
    #[inline(always)]
    fn to_bits(self) -> u64 {
        let () = FitsInHole::<T>::OK;
        let mut bits = 0u64;
        unsafe {
            core::ptr::copy_nonoverlapping(
                &self as *const T as *const u8,
                &mut bits as *mut u64 as *mut u8,
                core::mem::size_of::<T>(),
            )
        };
        bits
    }
    #[inline(always)]
    unsafe fn from_bits(bits: u64) -> Self {
        let () = FitsInHole::<T>::OK;
        unsafe { core::ptr::read_unaligned(&bits as *const u64 as *const T) }
    }
}

// ---- the Window trait -----------------------------------------------------

/// A copy&patch window op, as stored in `Residual::ExecWindow`.
pub trait Window: std::fmt::Debug {
    fn name(&self) -> &'static str;
    /// Number of window operands.
    fn arity(&self) -> usize;
    /// Stack slot each operand is loaded from, in window order.
    fn loads(&self) -> &[u16];
    /// Stack slot each operand is flushed to after the op, if any.
    fn stores(&self) -> &[Option<u16>];
    /// Hole values, in `__lunacy_holeN` order.
    fn captures(&self) -> Captures;
    /// Address of the stencil with the operands at window offset `k`.
    fn stencil(&self, k: usize) -> usize;
    /// Address of this op's `become` continuation (what every one of its
    /// stencils ends by jumping to, and what the copier slices off).
    fn next(&self) -> usize;
    /// Run the body on `ops` (this op's operands, in order) with the captures
    /// from `self`.
    unsafe fn run<'src, 'intern>(
        &self,
        owner: &mut Owner,
        state: &mut RunState<'src, 'intern>,
        base: *mut LBoxed<'src, 'intern>,
        ops: *mut LBoxed<'src, 'intern>,
    );
}

impl dyn Window {
    /// Interpreter tier: retrieve the operand slots, run the body, flush.
    pub fn interp<'src, 'intern>(&self, owner: &mut Owner, state: &mut RunState<'src, 'intern>) {
        let mut w = [LBoxed::NIL; WINDOW];
        for (i, &s) in self.loads().iter().enumerate() {
            w[i] = state.vals[state.base + s as usize];
        }
        let base = unsafe { state.vals.stack_ptr.as_non_null_ptr().add(state.base).as_ptr() };
        #[cfg(feature = "check_windows")]
        let before = w;
        unsafe { self.run(owner, state, base, w.as_mut_ptr()) };
        #[cfg(feature = "check_windows")]
        check::check(self, owner, state, base, before, &w);
        for (i, s) in self.stores().iter().enumerate() {
            if let Some(s) = s {
                state.vals[state.base + *s as usize] = w[i];
            }
        }
    }
}

// ---- windowed! ------------------------------------------------------------

#[doc(hidden)]
macro_rules! count_idents {
    () => { 0usize };
    ($h:ident $($t:ident)*) => { 1usize + $crate::window::count_idents!($($t)*) };
}
#[doc(hidden)]
pub(crate) use count_idents;

/// Bind each capture from its hole, `I` counting up from 0 at compile time.
#[doc(hidden)]
macro_rules! bind_holes {
    ($idx:expr;) => {};
    ($idx:expr; $cap:ident : $cty:ty $(, $rcap:ident : $rcty:ty)*) => {
        let $cap: $cty = unsafe {
            <$cty as $crate::window::Capture>::from_bits($crate::window::hole::<{ $idx }>())
        };
        $crate::window::bind_holes!($idx + 1; $($rcap : $rcty),*);
    };
}
#[doc(hidden)]
pub(crate) use bind_holes;

/// Declare a window op, usable at any emit site (like `define_exec!`):
///
/// ```ignore
/// windowed!(Name, [k: f64], [OP: Opcode], |owner, state, base| (a, b) {
///     *a = /* ... uses a, b, k, OP, owner, state, base ... */;
/// });
/// let w: Rc<dyn Window> = Rc::new(Name::<{ Opcode::ADD }>::new(k, &[lhs, rhs], &[Some(dest), None]));
/// ```
///
/// * `[captures]` — struct fields, and the stencil's holes (at most `MAX_HOLES`;
///   more fails at link time; any [`Capture`] type).
/// * `[const params]` — compile-time parameters baked into the stencil.
/// * `|owner, state, base|` — names for the fixed params.
/// * `(a, ...)` — the window operands, bound in the body as `&mut LBoxed`.
///
/// `new(captures.., loads, stores)` gives the stack slot each operand is loaded
/// from and (optionally) flushed to.
macro_rules! windowed {
    (
        $(#[$meta:meta])*
        $name:ident,
        [$($cap:ident : $cty:ty),* $(,)?],
        [$($cp:ident : $cpt:ty),* $(,)?],
        |$owner:ident, $state:ident, $base:ident| ($($op:ident),+ $(,)?)
        $body:block
    ) => {
        $(#[$meta])*
        #[derive(Debug, Clone)]
        pub struct $name<$(const $cp: $cpt),*> {
            $(pub $cap: $cty,)*
            /// Stack slot each window operand is loaded from, in window order.
            pub loads: ::smallvec::SmallVec<[u16; $crate::window::WINDOW]>,
            /// Stack slot each window operand is flushed to after the op.
            pub stores: ::smallvec::SmallVec<[Option<u16>; $crate::window::WINDOW]>,
        }

        #[allow(unused_variables, unused_mut, unused_assignments, unused_unsafe, clippy::too_many_arguments)]
        impl<$(const $cp: $cpt),*> $name<$($cp),*> {
            pub const ARITY: usize = $crate::window::count_idents!($($op)+);

            pub fn new($($cap: $cty,)* loads: &[u16], stores: &[Option<u16>]) -> Self {
                assert_eq!(loads.len(), Self::ARITY);
                assert_eq!(stores.len(), Self::ARITY);
                Self { $($cap,)* loads: loads.into(), stores: stores.into() }
            }

            /// The body, shared by the interpreter and the stencil.
            #[inline(always)]
            unsafe fn __run<'a, 'b, 'src, 'intern>(
                $($cap: $cty,)*
                $owner: &'a mut $crate::Owner,
                $state: &'b mut $crate::vm::RunState<'src, 'intern>,
                $base: *mut $crate::lboxed::LBoxed<'src, 'intern>,
                __ops: *mut $crate::lboxed::LBoxed<'src, 'intern>,
            ) {
                let mut __i = 0usize;
                $(
                    let $op: &mut $crate::lboxed::LBoxed<'src, 'intern> = unsafe { &mut *__ops.add(__i) };
                    __i += 1;
                )+
                unsafe { $body }
            }

            /// The stencil with this op's operands at window offset `K`.
            pub extern "rust-preserve-none" fn __stencil<'a, 'b, 'src, 'intern, const K: usize>(
                owner: &'a mut $crate::Owner,
                state: &'b mut $crate::vm::RunState<'src, 'intern>,
                base: *mut $crate::lboxed::LBoxed<'src, 'intern>,
                w0: $crate::lboxed::LBoxed<'src, 'intern>,
                w1: $crate::lboxed::LBoxed<'src, 'intern>,
                w2: $crate::lboxed::LBoxed<'src, 'intern>,
                w3: $crate::lboxed::LBoxed<'src, 'intern>,
            ) {
                if K + Self::ARITY > $crate::window::WINDOW {
                    // Never used: `stencil(k)` rejects such `k`.
                    unsafe { core::hint::unreachable_unchecked() }
                }
                let mut __w = [w0, w1, w2, w3];
                $crate::window::bind_holes!(0; $($cap : $cty),*);
                unsafe { Self::__run($($cap,)* &mut *owner, &mut *state, base, __w.as_mut_ptr().add(K)) };
                become Self::__next(owner, state, base, __w[0], __w[1], __w[2], __w[3])
            }

            /// This op's `become` target; the `jmp` to it is sliced off when
            /// copying, so it never runs. Per-op and private (and generic over
            /// the op's const params) so it is monomorphized next to the stencil
            /// with internal linkage, which makes the tail a direct `jmp rel32`: a
            /// shared exported continuation is reached through the GOT
            /// (`jmp *[rip+got]`) from other codegen units. `inline(never)` keeps
            /// the tail a real jump, and the body must visibly consume the whole
            /// window: an empty internal callee lets LLVM delete the tail call —
            /// and with it every computation feeding the window.
            #[inline(never)]
            extern "rust-preserve-none" fn __next<'a, 'b, 'src, 'intern>(
                owner: &'a mut $crate::Owner,
                state: &'b mut $crate::vm::RunState<'src, 'intern>,
                base: *mut $crate::lboxed::LBoxed<'src, 'intern>,
                w0: $crate::lboxed::LBoxed<'src, 'intern>,
                w1: $crate::lboxed::LBoxed<'src, 'intern>,
                w2: $crate::lboxed::LBoxed<'src, 'intern>,
                w3: $crate::lboxed::LBoxed<'src, 'intern>,
            ) {
                core::hint::black_box((owner as *mut $crate::Owner, state as *mut _, base, w0, w1, w2, w3));
            }
        }

        impl<$(const $cp: $cpt),*> $crate::window::Window for $name<$($cp),*> {
            fn name(&self) -> &'static str { stringify!($name) }
            fn arity(&self) -> usize { Self::ARITY }
            fn loads(&self) -> &[u16] { &self.loads }
            fn stores(&self) -> &[Option<u16>] { &self.stores }
            fn captures(&self) -> $crate::window::Captures {
                ::smallvec::smallvec![$($crate::window::Capture::to_bits(self.$cap)),*]
            }
            fn stencil(&self, k: usize) -> usize {
                assert!(k + Self::ARITY <= $crate::window::WINDOW, "{} at offset {k} overruns the window", stringify!($name));
                match k {
                    0 => Self::__stencil::<0> as *const () as usize,
                    1 => Self::__stencil::<1> as *const () as usize,
                    2 => Self::__stencil::<2> as *const () as usize,
                    3 => Self::__stencil::<3> as *const () as usize,
                    _ => unreachable!(),
                }
            }
            fn next(&self) -> usize { Self::__next as *const () as usize }
            unsafe fn run<'src, 'intern>(
                &self,
                owner: &mut $crate::Owner,
                state: &mut $crate::vm::RunState<'src, 'intern>,
                base: *mut $crate::lboxed::LBoxed<'src, 'intern>,
                ops: *mut $crate::lboxed::LBoxed<'src, 'intern>,
            ) {
                unsafe { Self::__run($(self.$cap,)* owner, state, base, ops) }
            }
        }
    };
}
pub(crate) use windowed;

// ---- copy&patch -----------------------------------------------------------

/// What the copier needs from this executable's own ELF image: each hole's GOT
/// slot and each function's size (to find the trailing `become`), at runtime
/// addresses.
pub struct Image {
    holes: [Option<usize>; MAX_HOLES],
    sizes: HashMap<usize, usize>,
}

impl Image {
    pub fn load() -> Self {
        let bytes = std::fs::read("/proc/self/exe").expect("read own executable");
        let elf = goblin::elf::Elf::parse(&bytes).expect("parse own ELF");

        let anchor = elf
            .syms
            .iter()
            .find(|s| elf.strtab.get_at(s.st_name) == Some("__lunacy_window_anchor"))
            .expect("window anchor in symtab")
            .st_value;
        let bias = (__lunacy_window_anchor as *const () as usize).wrapping_sub(anchor as usize);

        let hole_index = |name: &str| match name {
            "__lunacy_hole0" => Some(0),
            "__lunacy_hole1" => Some(1),
            _ => None,
        };
        let mut holes = [None; MAX_HOLES];
        // The GLOB_DAT relocation for a weak hole gives its GOT slot.
        for r in elf.dynrelas.iter() {
            let name = elf
                .dynsyms
                .get(r.r_sym)
                .and_then(|s| elf.dynstrtab.get_at(s.st_name))
                .unwrap_or("");
            if let Some(i) = hole_index(name) {
                holes[i] = Some(bias.wrapping_add(r.r_offset as usize));
            }
        }

        let sizes = elf
            .syms
            .iter()
            .filter(|s| s.is_function() && s.st_size != 0)
            .map(|s| (bias.wrapping_add(s.st_value as usize), s.st_size as usize))
            .collect();
        Image { holes, sizes }
    }
}

/// A RIP-relative reference in a stencil body: the `width`-byte displacement at
/// `field` is measured from the end of its instruction, `end`, and reaches the
/// absolute address `target`. Wherever the body is placed, rewrite the field so
/// it still reaches `target` (or, for a hole, its pool slot).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RipRel {
    pub field: usize,
    pub end: usize,
    pub width: usize,
    pub target: usize,
}

impl RipRel {
    /// Point this reference at `target`, with the body placed at `base`.
    /// Panics if `target` is out of rel32 range from there.
    fn patch(&self, code: &mut [u8], base: usize, target: usize) {
        assert_eq!(self.width, 4, "only 32-bit displacements can be re-targeted");
        let disp = (target as i64).wrapping_sub((base + self.end) as i64);
        let disp: i32 = disp
            .try_into()
            .unwrap_or_else(|_| panic!("{target:#x} is out of rel32 range of the copy at {base:#x}"));
        code[self.field..self.field + 4].copy_from_slice(&disp.to_le_bytes());
    }
}

/// A stencil's code with its trailing `become` sliced off, and every
/// RIP-relative reference in it.
pub struct Body {
    pub code: Vec<u8>,
    /// Hole loads (RIP-relative operands of a hole's GOT slot), with the hole
    /// index: repointed at the op's capture values in the shared pool.
    pub holes: SmallVec<[(RipRel, usize); MAX_HOLES]>,
    /// Every other RIP-relative reference: memory operands (GOT slots, rodata,
    /// ...) and relative calls/jumps leaving the body. They must keep reaching
    /// their absolute `target` wherever the body is copied; the JIT hands them to
    /// dynasm as relocations patched in `finalize` along with the hole pool (JIT
    /// memory is mapped within ±2GiB of the binary, so rel32 still reaches).
    pub relocs: Vec<RipRel>,
    /// References to the op's continuation besides the sliced trailing
    /// `become` — e.g. a tail the compiler duplicated onto another path. Every
    /// `become` means "fall through to the next stencil", so each must reach the
    /// copy's fall-through point (its end); the JIT relocates them against a
    /// label there.
    pub nexts: Vec<NextRef>,
}

/// A reference to the continuation inside a stencil body.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NextRef {
    /// A `jmp rel32` to it (or a `lea` of its address): re-target at the
    /// fall-through point itself.
    Direct(RipRel),
    /// A load from a GOT slot holding it (`mov reg, [rip+got]` feeding a
    /// `jmp *reg`, or `jmp *[rip+got]`): repoint at a pool slot holding the
    /// fall-through point's address.
    Indirect(RipRel),
}

impl Body {
    /// The non-hole RIP-relative references to re-target when this body is
    /// placed somewhere else.
    pub fn relocations(&self) -> &[RipRel] {
        &self.relocs
    }
}

/// Opcodes whose first operand is a relative branch target (mirrors
/// yaxpeax-x86's private `RELATIVE_BRANCHES`).
const RELATIVE_BRANCHES: [yaxpeax_x86::long_mode::Opcode; 23] = {
    use yaxpeax_x86::long_mode::Opcode::*;
    [
        JMP, CALL, JRCXZ, JECXZ, LOOP, LOOPZ, LOOPNZ, JO, JNO, JB, JNB, JZ, JNZ, JNA, JA, JS, JNS,
        JP, JNP, JL, JGE, JLE, JG,
    ]
};

/// Copy `op`'s stencil at window offset `k`.
///
/// A well-formed stencil ends in its `become`: its last instruction is a tail
/// jump to the op's continuation, which is sliced off so the next stencil falls
/// through. The rest is decoded to find every RIP-relative reference: loads of a
/// hole's GOT slot are holes, the rest are relocations. Branches that stay within
/// the body need no fixup (one to the sliced tail becomes a fall-through into the
/// next stencil, as it should).
pub unsafe fn stencil_body(image: &Image, op: &dyn Window, k: usize) -> Body {
    use yaxpeax_arch::LengthedInstruction;
    use yaxpeax_x86::long_mode::{InstDecoder, Instruction, Opcode, Operand, RegSpec};

    let addr = op.stencil(k);
    let size = *image.sizes.get(&addr).expect("stencil in symtab");
    let code = unsafe { core::slice::from_raw_parts(addr as *const u8, size) };
    let name = op.name();

    // Decode the whole stencil: (offset, end, instruction).
    let decoder = InstDecoder::default();
    let mut insts: Vec<(usize, usize, Instruction)> = Vec::new();
    let mut off = 0;
    while off < size {
        let inst = decoder
            .decode_slice(&code[off..])
            .unwrap_or_else(|e| panic!("{name}: undecodable stencil byte at +{off:#x}: {e}"));
        let end = off + inst.len().to_const() as usize;
        insts.push((off, end, inst));
        off = end;
    }
    assert_eq!(off, size, "{name}: stencil doesn't end on an instruction boundary");

    // An instruction's RIP-relative memory operand, as (disp field offset,
    // absolute target). The displacement is followed only by the instruction's
    // immediate (if any), so it sits just before it.
    let rip_operand = |off: usize, end: usize, inst: &Instruction| -> Option<(usize, usize)> {
        let mut imm_bytes = 0;
        let mut disp = None;
        for i in 0..inst.operand_count() {
            match inst.operand(i) {
                Operand::ImmediateI8 { .. } | Operand::ImmediateU8 { .. } => imm_bytes += 1,
                Operand::ImmediateI16 { .. } | Operand::ImmediateU16 { .. } => imm_bytes += 2,
                Operand::ImmediateI32 { .. } | Operand::ImmediateU32 { .. } => imm_bytes += 4,
                Operand::Disp { base, disp: d } | Operand::DispMasked { base, disp: d, .. }
                    if base == RegSpec::RIP =>
                {
                    disp = Some(d)
                }
                _ => {}
            }
        }
        let disp = disp?;
        let field = end - imm_bytes - 4;
        assert_eq!(
            i32::from_le_bytes(code[field..field + 4].try_into().unwrap()),
            disp,
            "{name}: RIP displacement not where expected at +{off:#x}"
        );
        Some((field, (addr + end).wrapping_add(disp as isize as usize)))
    };

    // Whether instruction `i` jumps to the continuation. rustc builds with
    // `-Z plt=no`, so depending on whether the continuation is known to be local
    // that's `jmp rel32`, `jmp *[rip+got]`, or `jmp *reg` with `reg` loaded from
    // the GOT slot earlier (LLVM hoists that load above the epilogue). A GOT slot
    // holds the loader-relocated address, so read it to check.
    let next = op.next();
    let got = |slot: usize| unsafe { core::ptr::read_unaligned(slot as *const usize) };
    let jumps_to_next = |i: usize| {
        let (off, end, inst) = &insts[i];
        inst.opcode() == Opcode::JMP
            && match inst.operand(0) {
                Operand::ImmediateI32 { imm } => (addr + end).wrapping_add(imm as isize as usize) == next,
                Operand::Register { reg } => insts[..i]
                    .iter()
                    .rev()
                    .take_while(|(_, _, i)| i.opcode() != Opcode::CALL)
                    .find(|(_, _, i)| {
                        i.operand_count() > 0 && matches!(i.operand(0), Operand::Register { reg: r } if r == reg)
                    })
                    .is_some_and(|(o, e, i)| {
                        i.opcode() == Opcode::MOV && rip_operand(*o, *e, i).is_some_and(|(_, t)| got(t) == next)
                    }),
                _ => rip_operand(*off, *end, inst).is_some_and(|(_, t)| got(t) == next),
            }
    };

    // The tail: the last instruction must jump to the continuation.
    let last = insts.len() - 1;
    assert!(jumps_to_next(last), "{name} stencil at offset {k} does not end in `become` to its continuation");
    let body_len = insts[last].0;

    let mut holes = SmallVec::new();
    let mut relocs = Vec::new();
    let mut nexts = Vec::new();
    for (i, (off, end, inst)) in insts[..last].iter().enumerate() {
        let (off, end) = (*off, *end);
        // Relative branches: operand 0 is the displacement from `end`.
        let rel = match inst.operand(0) {
            Operand::ImmediateI8 { imm } => Some((imm as i64, 1)),
            Operand::ImmediateI32 { imm } => Some((imm as i64, 4)),
            _ => None,
        };
        match rel {
            Some((rel, width)) if RELATIVE_BRANCHES.contains(&inst.opcode()) => {
                let target = (addr + end).wrapping_add(rel as isize as usize);
                if !(addr..=addr + body_len).contains(&target) {
                    assert_eq!(width, 4, "{name}: short branch leaves the stencil");
                    let rel = RipRel { field: end - 4, end, width, target };
                    if target == next {
                        // Another `become` (e.g. a duplicated tail).
                        nexts.push(NextRef::Direct(rel));
                    } else if inst.opcode() == Opcode::CALL {
                        relocs.push(rel);
                    } else {
                        // A jump out that isn't a `become` never falls through
                        // to the next stencil (e.g. a sibling tail call).
                        panic!("{name}: stencil at offset {k} jumps out to {target:#x} at +{off:#x}");
                    }
                }
            }
            // An indirect jump that isn't a `become` (e.g. through a jump table,
            // whose entries lead back into the original function) can't be
            // followed, so the copy would leave the chain.
            _ if inst.opcode() == Opcode::JMP && !jumps_to_next(i) => {
                panic!("{name}: stencil at offset {k} has an indirect jump (jump table?) at +{off:#x}");
            }
            _ => {}
        }
        // RIP-relative memory operands: a hole's GOT slot, the continuation (its
        // address, or a slot holding it), or anything else.
        if let Some((field, target)) = rip_operand(off, end, inst) {
            let rel = RipRel { field, end, width: 4, target };
            if let Some(i) = image.holes.iter().position(|h| *h == Some(target)) {
                holes.push((rel, i));
            } else if inst.opcode() == Opcode::LEA && target == next {
                nexts.push(NextRef::Direct(rel));
            } else if inst.opcode() != Opcode::LEA && got(target) == next {
                nexts.push(NextRef::Indirect(rel));
            } else {
                relocs.push(rel);
            }
        }
    }
    Body { code: code[..body_len].to_vec(), holes, relocs, nexts }
}

/// A mapping hint within ±2GiB of this binary with room for `len` bytes, so
/// rel32 references in copied stencils still reach their targets (the same
/// placement the JIT's code buffer uses).
fn near_hint(len: usize) -> *mut core::ffi::c_void {
    let target = __lunacy_window_anchor as *const () as usize;
    let len = len.next_multiple_of(4096);
    let max = 1usize << 31;
    rsprocmaps::from_path("/proc/self/maps")
        .unwrap()
        .map_windows(|[first, second]| {
            let (Ok(first), Ok(second)) = (first, second) else { return None };
            let start = first.address_range.end as usize;
            let gap = (second.address_range.begin as usize).saturating_sub(start);
            (gap >= len && target.abs_diff(start) + len < max).then_some(start)
        })
        .flatten()
        .next()
        .expect("no free mapping within rel32 range of the binary") as *mut _
}

/// Copy&patch `ops` — each a window op and the window offset its operands sit
/// at — into one executable buffer near the binary: bodies concatenated (so the
/// register window falls through), then `tail`, then the shared pool of hole
/// values. Every hole is repointed at its pool slot, every reference to an op's
/// continuation at that copy's fall-through point (the next stencil), and every
/// other RIP-relative reference is re-targeted at its original absolute address.
pub unsafe fn assemble(image: &Image, ops: &[(&dyn Window, usize)], tail: &[u8]) -> ExecutableBuffer {
    let mut code = Vec::new();
    let mut holes: Vec<(RipRel, u64)> = Vec::new();
    let mut relocs: Vec<RipRel> = Vec::new();
    // Each continuation reference, with its copy's fall-through offset.
    let mut nexts: Vec<(NextRef, usize)> = Vec::new();
    for &(op, k) in ops {
        let body = unsafe { stencil_body(image, op, k) };
        let captures = op.captures();
        let at = code.len();
        let shift = |r: RipRel| RipRel { field: r.field + at, end: r.end + at, ..r };
        code.extend_from_slice(&body.code);
        let fall = code.len();
        holes.extend(body.holes.iter().map(|&(r, i)| (shift(r), captures[i])));
        relocs.extend(body.relocs.iter().map(|&r| shift(r)));
        nexts.extend(body.nexts.iter().map(|n| match *n {
            NextRef::Direct(r) => (NextRef::Direct(shift(r)), fall),
            NextRef::Indirect(r) => (NextRef::Indirect(shift(r)), fall),
        }));
    }
    code.extend_from_slice(tail);
    while code.len() % 8 != 0 {
        code.push(0xcc);
    }
    // The pool: hole values, then one slot per indirect continuation reference
    // (filled with its fall-through address once the buffer's address is known).
    let pool = code.len();
    for &(_, val) in &holes {
        code.extend_from_slice(&val.to_le_bytes());
    }
    let indirect = nexts.iter().filter(|(n, _)| matches!(n, NextRef::Indirect(_))).count();
    code.resize(code.len() + indirect * 8, 0);

    let mut buf = MutableBuffer::new_with_hint(code.len(), near_hint(code.len())).unwrap();
    buf.set_len(code.len());
    let base = buf.as_mut_ptr() as usize;
    for (i, (r, _)) in holes.iter().enumerate() {
        r.patch(&mut code, base, base + pool + i * 8);
    }
    let mut slot = pool + holes.len() * 8;
    for &(n, fall) in &nexts {
        match n {
            NextRef::Direct(r) => r.patch(&mut code, base, base + fall),
            NextRef::Indirect(r) => {
                code[slot..slot + 8].copy_from_slice(&((base + fall) as u64).to_le_bytes());
                r.patch(&mut code, base, base + slot);
                slot += 8;
            }
        }
    }
    for r in &relocs {
        r.patch(&mut code, base, r.target);
    }
    unsafe { core::ptr::copy_nonoverlapping(code.as_ptr(), buf.as_mut_ptr(), code.len()) };
    buf.make_exec().unwrap()
}

/// Differential check (feature `check_windows`): every window op the interpreter
/// runs is also copy&patched and run as native code on the same operands, and
/// the results must match bit for bit. This drives the ops the specializer
/// actually emits — declared at their emit sites, so no test can name them —
/// through the real copier. It re-executes the op, so it assumes the op's
/// effects are confined to its window. Needs optimized stencils: run via
/// `just test-stencils`.
#[cfg(feature = "check_windows")]
mod check {
    use super::*;
    use dynasmrt::AssemblyOffset;
    use std::cell::RefCell;

    // Writes the window to the address in its capture (a hole), so observing the
    // result doesn't depend on `base`, which the op under test may use.
    windowed!(CheckFlush, [out: u64], [], |owner, state, base| (a, b, c, d) {
        let out = out as *mut u64;
        *out.add(0) = a.bits();
        *out.add(1) = b.bits();
        *out.add(2) = c.bits();
        *out.add(3) = d.bits();
    });

    struct Checker {
        image: Image,
        out: *mut [u64; WINDOW],
        programs: HashMap<(usize, Captures), ExecutableBuffer>,
    }

    thread_local! {
        static CHECKER: RefCell<Option<Checker>> = const { RefCell::new(None) };
    }

    pub(super) fn check<'src, 'intern>(
        op: &dyn Window,
        owner: &mut Owner,
        state: &mut RunState<'src, 'intern>,
        base: *mut LBoxed<'src, 'intern>,
        before: [LBoxed<'src, 'intern>; WINDOW],
        after: &[LBoxed<'src, 'intern>; WINDOW],
    ) {
        CHECKER.with_borrow_mut(|c| {
            let c = c.get_or_insert_with(|| Checker {
                image: Image::load(),
                out: Box::leak(Box::new([0u64; WINDOW])),
                programs: HashMap::new(),
            });
            let flush = CheckFlush::new(c.out as u64, &[0; WINDOW], &[None; WINDOW]);
            let image = &c.image;
            let exec = c
                .programs
                .entry((op.stencil(0), op.captures()))
                .or_insert_with(|| unsafe { assemble(image, &[(op, 0), (&flush, 0)], &[0xc3]) });
            let entry: extern "rust-preserve-none" fn(
                &mut Owner,
                &mut RunState<'src, 'intern>,
                *mut LBoxed<'src, 'intern>,
                LBoxed<'src, 'intern>,
                LBoxed<'src, 'intern>,
                LBoxed<'src, 'intern>,
                LBoxed<'src, 'intern>,
            ) = unsafe { core::mem::transmute(exec.ptr(AssemblyOffset(0))) };
            entry(owner, state, base, before[0], before[1], before[2], before[3]);
            let native = unsafe { *c.out };
            let interp: [u64; WINDOW] = core::array::from_fn(|i| after[i].bits());
            assert_eq!(native, interp, "{}: copy&patched stencil disagrees with the interpreter", op.name());
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dynasmrt::AssemblyOffset;

    // Test-local window ops, declared exactly as an emit site would.
    windowed!(TAdd, [], [], |owner, state, base| (a, b) {
        *a = LBoxed::from_number(a.as_number().unwrap_unchecked() + b.as_number().unwrap_unchecked());
    });
    windowed!(TMul, [], [], |owner, state, base| (a, b) {
        *a = LBoxed::from_number(a.as_number().unwrap_unchecked() * b.as_number().unwrap_unchecked());
    });
    windowed!(TAddK, [k: f64], [], |owner, state, base| (a) {
        *a = LBoxed::from_number(a.as_number().unwrap_unchecked() + k);
    });
    // Flush the whole window to `base[0..WINDOW]`, to observe the result.
    windowed!(Flush, [], [], |owner, state, base| (a, b, c, d) {
        *base.add(0) = *a;
        *base.add(1) = *b;
        *base.add(2) = *c;
        *base.add(3) = *d;
    });

    // A stencil that calls out of line (as table get/set through `IndexMap`
    // will): the call is a non-hole RIP-relative reference the copier must
    // re-target.
    #[inline(never)]
    extern "C" fn out_of_line(x: f64) -> f64 {
        core::hint::black_box(x * 3.0 + 1.0)
    }
    windowed!(TCall, [], [], |owner, state, base| (a) {
        *a = LBoxed::from_number(out_of_line(a.as_number().unwrap_unchecked()));
    });

    // A branchy stencil: one arm calls out, the other doesn't, which invites the
    // compiler to duplicate the `become` onto each path.
    windowed!(TBranch, [], [], |owner, state, base| (a) {
        let x = a.as_number().unwrap_unchecked();
        if x < 0.0 {
            *a = LBoxed::from_number(out_of_line(x));
        } else {
            *a = LBoxed::from_number(x + 100.0);
        }
    });

    /// Both arms of a branchy stencil fall through to the next stencil, however
    /// many `become`s the compiler left in it.
    #[test]
    fn copy_and_patch_branches() {
        let image = Image::load();
        let branch = TBranch::new(&[0], &[None]);
        let flush = Flush::new(&[0; 4], &[None; 4]);
        let exec = unsafe { assemble(&image, &[(&branch, 0), (&flush, 0)], &[0xc3]) };
        for (x, want) in [(-2.0, -5.0), (2.0, 102.0)] {
            let mut out = [LBoxed::NIL; WINDOW];
            entry_of(&exec)(0, 0, out.as_mut_ptr(), LBoxed::from_number(x), LBoxed::NIL, LBoxed::NIL, LBoxed::NIL);
            assert_eq!(out[0].as_number(), Some(want), "input {x}");
        }
    }

    fn entry_of(exec: &ExecutableBuffer) -> extern "rust-preserve-none" fn(
        usize,
        usize,
        *mut LBoxed<'static, 'static>,
        LBoxed<'static, 'static>,
        LBoxed<'static, 'static>,
        LBoxed<'static, 'static>,
        LBoxed<'static, 'static>,
    ) {
        // Same ABI as a stencil, with the (unused here) owner/state as raw words.
        unsafe { core::mem::transmute(exec.ptr(AssemblyOffset(0))) }
    }

    /// The out-of-line call shows up in `relocations()` (directly, or through
    /// the GOT slot it calls through), and the copy still calls it correctly.
    #[test]
    fn copy_and_patch_relocates_calls() {
        let image = Image::load();
        let call = TCall::new(&[0], &[None]);
        let flush = Flush::new(&[0; 4], &[None; 4]);

        let helper = out_of_line as *const () as usize;
        let body = unsafe { stencil_body(&image, &call, 0) };
        assert!(
            body.relocations().iter().any(|r| r.target == helper
                || unsafe { *(r.target as *const usize) } == helper),
            "call to the helper not among {:x?}",
            body.relocations()
        );

        let exec = unsafe { assemble(&image, &[(&call, 0), (&flush, 0)], &[0xc3]) };
        let mut out = [LBoxed::NIL; WINDOW];
        entry_of(&exec)(0, 0, out.as_mut_ptr(), LBoxed::from_number(2.0), LBoxed::NIL, LBoxed::NIL, LBoxed::NIL);
        assert_eq!(out[0].as_number(), Some(7.0));
    }

    /// Copy&patch a chain over the register window and run it: prepare
    /// (a, b, c), Add at offset 1 (b+c), Mul at offset 0 (a*prev), AddK at offset
    /// 0 (a capture/hole), then Flush.
    #[test]
    fn copy_and_patch_chain() {
        let image = Image::load();
        let add = TAdd::new(&[0, 0], &[None, None]);
        let mul = TMul::new(&[0, 0], &[None, None]);
        let addk = TAddK::new(0.5, &[0], &[None]);
        let flush = Flush::new(&[0; 4], &[None; 4]);
        let ops: [(&dyn Window, usize); 4] = [(&add, 1), (&mul, 0), (&addk, 0), (&flush, 0)];
        let exec = unsafe { assemble(&image, &ops, &[0xc3]) };
        let entry = entry_of(&exec);

        let mut out = [LBoxed::NIL; WINDOW];
        entry(
            0,
            0,
            out.as_mut_ptr(),
            LBoxed::from_number(2.0),
            LBoxed::from_number(3.0),
            LBoxed::from_number(4.0),
            LBoxed::NIL,
        );
        assert_eq!(out[0].as_number(), Some(2.0 * (3.0 + 4.0) + 0.5));
        assert_eq!(out[1].as_number(), Some(7.0));
        assert_eq!(out[2].as_number(), Some(4.0));
        assert!(!out[3].is_number());
    }
}
