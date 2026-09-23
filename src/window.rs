//! Copy&patch register-window ops. See `docs/jit-register-cache.md`.
//!
//! The mechanism is op-agnostic: any emit site declares its own window op with
//! [`windowed!`], exactly as it would a `define_exec!` closure. That produces:
//!
//! * a struct whose fields are the op's **captures** (its holes' values) plus the
//!   stack slots of its operands, and which implements [`Window`] — a trait
//!   object the specializer stores in `Residual::ExecWindow`, so no processing
//!   site enumerates ops (like `Exec`'s closure);
//! * an `#[inline(always)]` body shared by both tiers (single source of truth);
//! * a `rust-preserve-none` stencil `__stencil::<SKIP>`: the fixed params
//!   `(owner, state, base)` (the ABI the JIT pins in r12/r13/r14) followed by the
//!   register window as **scalar** `LBoxed` params `w0..w7` (r15, rdi, rsi, rdx, rcx, r8, r9, r11; see
//!   `WINDOW`).
//!   Scalars, not `[LBoxed; N]`, because Rust passes arrays by pointer whatever
//!   the ABI, which would put the window in memory. Operand `i`, in the order
//!   the op declares them, is `w[SKIP + i]` (see Note [Register window]).
//!   The stencil ends in `become` to
//!   the op's own continuation, which the copier slices off so the window falls
//!   through into the next stencil.
//!
//! Captures reach the stencil through `extern_weak` hole statics (`__lunacy_holeN`).
//! Under plain PIE each read is a RIP-relative load from the hole's GOT slot; the
//! copier finds those loads via this executable's own dynamic relocations (goblin)
//! and repoints them at a shared value pool laid after the code. The interpreter
//! tier cannot run the stencil itself (its holes read 0 until patched), so it runs
//! the same body with captures from the struct.
//!
//! Copying a stencil (`stencil_body`) decodes it (yaxpeax-x86). Every exit of a
//! well-formed stencil is its `become`, a tail jump to the op's continuation,
//! which the copy redirects to its end so the next stencil falls through (a
//! final `become` is simply sliced off). Every other
//! RIP-relative reference in the body is reported so it can be re-targeted
//! wherever the body lands: hole loads (repointed at the op's capture values),
//! other continuation references (at the copy's fall-through point), and
//! everything else — calls out of line (e.g. into `IndexMap`), GOT slots,
//! rodata — at its original absolute address, which stays in rel32 range because
//! JIT memory is mapped within ±2GiB of the binary. In the JIT these all become
//! dynasm relocations patched at `finalize`; `assemble` does the same by hand.
//! Calls are fine anywhere (they return), but a jump that leaves the stencil
//! without being a `become` would skip the rest of the chain, so it is rejected
//! with a [`StencilError`]: a sibling tail call, or an indirect jump such as a
//! jump table (whose entries lead back into the original function). An opt-level
//! 0 build of `NumericIntInt` hits the latter (`match OP` isn't folded);
//! optimized builds don't. The interpreter tier runs any window op regardless,
//! and the JIT calls the body of an op the copier rejects.

// Note [Register window]
// ~~~~~~~~~~~~~~~~~~~~~~
// A window op's operands are whole `LBoxed` values held in the register window:
// `WINDOW` registers, passed between stencils as the scalar params `w0..w7`. An
// op always runs on a contiguous run of the window: operand `i`, in the order
// the op declares its operands, is register `SKIP + i`, and
// `Window::stencil(skip)` is the instance for that `SKIP`. The order is the op's
// choice (e.g. its output last, where the next op can start); the allocator
// handles any.
// An op's inputs are read-only and only its outputs are written, so the
// registers outside its run, and its inputs, keep their values. An op's body
// must reach this frame's stack slots only through its operands: any of them
// may have a newer value in a register than in its stack home.
//
// The specializer never chooses registers: the emit site builds the op from
// its operands' stack slots, and its `ExecWindow` is the only residual.
//
// The JIT allocates registers (`crate::window_alloc`) at each `ExecWindow`,
// knowing all of its operands from the op: it picks `SKIP` and resculpts the
// window from `SKIP` on: each
// input is moved there from the register already caching its slot, or loaded
// from the slot's stack home, and cached values displaced from the run are moved
// to spare registers or evicted. A register holding the only copy of a slot's
// current value is dirty until flushed to the stack home, at an eviction or when
// the run of window residuals ends. An inline type guard does not end the run:
// it tests the cached register, and stores the dirty ones on its failure path.
//
// The interpreter keeps no window between residuals: `ExecWindow` runs the op at
// `SKIP` 0, loading its inputs from their stack homes and flushing its outputs,
// so resuming a block at any residual is sound.

use std::collections::HashMap;

use dynasmrt::mmap::{ExecutableBuffer, MutableBuffer};
use smallvec::SmallVec;

use crate::lboxed::LBoxed;
use crate::vm::RunState;
use crate::Owner;

/// Number of register-window slots (w0..w7 = r15, rdi, rsi, rdx, rcx, r8, r9, r11).
/// `rust-preserve-none` passes 12 integer arguments in registers, 3 of them the
/// fixed params, but the 12th (rax) can't be a window register: a stencil's
/// `become` may be an indirect jump through the GOT, whose target LLVM loads
/// into rax even when rax carries an argument, and that load stays in the copy.
pub const WINDOW: usize = 8;
/// Number of hole statics available to captures.
pub const MAX_HOLES: usize = 2;
// `Captures` and `Regs` use literal lengths: with `generic_const_exprs` on, a named
// const in a trait method signature makes `Window` dyn-incompatible.
/// A window op's hole values.
pub type Captures = SmallVec<[u64; 2]>;
/// The register window's values.
pub type Regs<'src, 'intern> = [LBoxed<'src, 'intern>; 8];
const _: () = assert!(MAX_HOLES == 2 && WINDOW == 8);

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

// ---- operands -------------------------------------------------------------

/// How an op uses one of its operands' slots.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Access {
    /// The op reads the slot's value.
    Read,
    /// The op only writes the slot.
    Write,
}

/// Check a window op's operand slots against its operands' accesses: no two
/// outputs write the same slot.
#[doc(hidden)]
pub fn check_operands(name: &str, operands: &[usize], accesses: &[Access]) {
    let outputs = || operands.iter().zip(accesses).filter(|(_, a)| **a == Access::Write).map(|(slot, _)| *slot);
    for (i, a) in outputs().enumerate() {
        assert!(outputs().skip(i + 1).all(|b| b != a), "{name}: two outputs write slot {a}");
    }
}

// ---- the Window trait -----------------------------------------------------

/// A copy&patch window op, as stored in `Residual::ExecWindow`.
pub trait Window: std::fmt::Debug {
    fn name(&self) -> &'static str;
    /// The operands' stack slots, relative to the frame's base, in the order the
    /// op declares them: operand `i` is window register `SKIP + i`.
    fn operands(&self) -> &[usize];
    /// Whether each operand is read (an input) or written (an output).
    fn accesses(&self) -> &'static [Access];
    /// Hole values, in `__lunacy_holeN` order.
    fn captures(&self) -> Captures;
    /// Number of operands: the op runs on `w[skip..skip + arity()]`.
    fn arity(&self) -> usize;
    /// Address of the stencil running at `skip`.
    fn stencil(&self, skip: usize) -> usize;
    /// Address of this op's `become` continuation (what every one of its
    /// stencils ends by jumping to, and what the copier slices off).
    fn next(&self) -> usize;
    /// Run the body on the window `w` at `skip`, with the captures from `self`.
    unsafe fn run<'src, 'intern>(
        &self,
        owner: &mut Owner,
        state: &mut RunState<'src, 'intern>,
        base: *mut LBoxed<'src, 'intern>,
        w: &mut Regs<'src, 'intern>,
        skip: usize,
    );
}

impl dyn Window {
    /// Interpreter tier: load the inputs from their stack homes, run the body,
    /// flush the outputs. See Note [Register window].
    pub fn interp<'src, 'intern>(&self, owner: &mut Owner, state: &mut RunState<'src, 'intern>) {
        let operands = self.operands().iter().zip(self.accesses()).enumerate();
        let mut w = [LBoxed::NIL; WINDOW];
        for (i, (slot, _)) in operands.clone().filter(|(_, (_, a))| **a == Access::Read) {
            w[i] = state.vals[state.base + slot];
        }
        let base = unsafe { state.vals.stack_ptr.as_non_null_ptr().add(state.base).as_ptr() };
        #[cfg(feature = "check_windows")]
        let before = w;
        unsafe { self.run(owner, state, base, &mut w, 0) };
        #[cfg(feature = "check_windows")]
        check::check(self, owner, state, base, before, &w);
        for (i, (slot, _)) in operands.filter(|(_, (_, a))| **a == Access::Write) {
            state.vals[state.base + slot] = w[i];
        }
    }
}

// ---- windowed! ------------------------------------------------------------

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
/// windowed!(Name, [k: f64], [OP: Opcode], |owner, state, base| (out d, a, b) {
///     *d = /* ... uses a, b, k, OP, owner, state, base ... */;
/// });
/// let w: Rc<dyn Window> = Rc::new(Name::<{ Opcode::ADD }>::new(k, &[d, a, b])); // slots
/// ```
///
/// * `[captures]` — struct fields, and the stencil's holes (at most `MAX_HOLES`;
///   more fails at link time; any [`Capture`] type).
/// * `[const params]` — compile-time parameters baked into the stencil.
/// * `|owner, state, base|` — names for the fixed params.
/// * `(operands)` — the window operands in window order: operand `i` is register
///   `SKIP + i`. An input is bound in the body as an `LBoxed` value, an output
///   (marked `out`) as `&mut LBoxed` to write the result to. The body must not
///   otherwise read or write this frame's stack slots (see Note [Register
///   window]).
///
/// `new(captures.., operands)` takes the operands' stack slots in the same
/// order. See Note [Register window].
macro_rules! windowed {
    (
        $(#[$meta:meta])*
        $name:ident,
        [$($cap:ident : $cty:ty),* $(,)?],
        [$($cp:ident : $cpt:ty),* $(,)?],
        |$owner:ident, $state:ident, $base:ident| ($($operands:tt)*)
        $body:block
    ) => {
        $crate::window::windowed!(@sort
            [$(#[$meta])* $name, [$($cap : $cty),*], [$($cp : $cpt),*], |$owner, $state, $base| $body]
            [] [] [] (0usize) $($operands)*
        );
    };
    // Sort the operands into inputs and outputs, each with its window offset,
    // and their accesses in window order.
    (@sort $decl:tt [$($in:tt)*] [$($out:tt)*] [$($acc:tt)*] ($i:expr) out $op:ident $(, $($rest:tt)*)?) => {
        $crate::window::windowed!(@sort $decl [$($in)*] [$($out)* ($op, $i)] [$($acc)* Write] ($i + 1) $($($rest)*)?);
    };
    (@sort $decl:tt [$($in:tt)*] [$($out:tt)*] [$($acc:tt)*] ($i:expr) $op:ident $(, $($rest:tt)*)?) => {
        $crate::window::windowed!(@sort $decl [$($in)* ($op, $i)] [$($out)*] [$($acc)* Read] ($i + 1) $($($rest)*)?);
    };
    (@sort
        [$(#[$meta:meta])* $name:ident, [$($cap:ident : $cty:ty),*], [$($cp:ident : $cpt:ty),*], |$owner:ident, $state:ident, $base:ident| $body:block]
        [$(($in:ident, $ii:expr))*] [$(($out:ident, $oi:expr))*] [$($acc:ident)*] ($arity:expr)
    ) => {
        $(#[$meta])*
        #[derive(Debug, Clone)]
        pub struct $name<$(const $cp: $cpt),*> {
            $(pub $cap: $cty,)*
            operands: ::smallvec::SmallVec<[usize; $crate::window::WINDOW]>,
        }

        #[allow(unused_variables, unused_mut, unused_assignments, unused_unsafe, clippy::too_many_arguments)]
        impl<$(const $cp: $cpt),*> $name<$($cp),*> {
            pub const ARITY: usize = $arity;
            const ACCESSES: &'static [$crate::window::Access] = &[$($crate::window::Access::$acc),*];
            const FITS: () = assert!(Self::ARITY <= $crate::window::WINDOW, "more operands than window registers");

            /// `operands`: the operands' stack slots, in window order.
            pub fn new($($cap: $cty,)* operands: &[usize]) -> Self {
                let () = Self::FITS;
                assert_eq!(operands.len(), Self::ARITY, "{}: wrong number of operands", stringify!($name));
                $crate::window::check_operands(stringify!($name), operands, Self::ACCESSES);
                Self { $($cap,)* operands: operands.into() }
            }

            /// The body, shared by the interpreter and the stencil.
            #[inline(always)]
            unsafe fn __run<'a, 'b, 'src, 'intern>(
                $($cap: $cty,)*
                $owner: &'a mut $crate::Owner,
                $state: &'b mut $crate::vm::RunState<'src, 'intern>,
                $base: *mut $crate::lboxed::LBoxed<'src, 'intern>,
                $($in: $crate::lboxed::LBoxed<'src, 'intern>,)*
                $($out: &mut $crate::lboxed::LBoxed<'src, 'intern>,)*
            ) {
                unsafe { $body }
            }

            /// Run the body on the window `w` at `skip`: read the inputs, write
            /// back only the outputs.
            #[inline(always)]
            unsafe fn __window<'a, 'b, 'src, 'intern>(
                $($cap: $cty,)*
                owner: &'a mut $crate::Owner,
                state: &'b mut $crate::vm::RunState<'src, 'intern>,
                base: *mut $crate::lboxed::LBoxed<'src, 'intern>,
                w: &mut [$crate::lboxed::LBoxed<'src, 'intern>; $crate::window::WINDOW],
                skip: usize,
            ) {
                $( let $in = w[skip + $ii]; )*
                $( let mut $out = w[skip + $oi]; )*
                unsafe { Self::__run($($cap,)* owner, state, base, $($in,)* $(&mut $out,)*) };
                $( w[skip + $oi] = $out; )*
            }

            /// The stencil running at `SKIP`.
            pub extern "rust-preserve-none" fn __stencil<'a, 'b, 'src, 'intern, const SKIP: usize>(
                owner: &'a mut $crate::Owner,
                state: &'b mut $crate::vm::RunState<'src, 'intern>,
                base: *mut $crate::lboxed::LBoxed<'src, 'intern>,
                w0: $crate::lboxed::LBoxed<'src, 'intern>,
                w1: $crate::lboxed::LBoxed<'src, 'intern>,
                w2: $crate::lboxed::LBoxed<'src, 'intern>,
                w3: $crate::lboxed::LBoxed<'src, 'intern>,
                w4: $crate::lboxed::LBoxed<'src, 'intern>,
                w5: $crate::lboxed::LBoxed<'src, 'intern>,
                w6: $crate::lboxed::LBoxed<'src, 'intern>,
                w7: $crate::lboxed::LBoxed<'src, 'intern>,
            ) {
                if SKIP + Self::ARITY > $crate::window::WINDOW {
                    // Never used: `stencil(skip)` rejects such `skip`.
                    unsafe { core::hint::unreachable_unchecked() }
                }
                let mut w = [w0, w1, w2, w3, w4, w5, w6, w7];
                $crate::window::bind_holes!(0; $($cap : $cty),*);
                unsafe { Self::__window($($cap,)* &mut *owner, &mut *state, base, &mut w, SKIP) };
                become Self::__next(owner, state, base, w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7])
            }

            /// This op's `become` target; the `jmp` to it is sliced off when
            /// copying, so it never runs. Per-op and private (and generic over
            /// the op's const params) so it is monomorphized next to the stencil
            /// with internal linkage, which makes the tail a direct `jmp rel32`: a
            /// shared exported continuation is reached through the GOT
            /// (`jmp *[rip+got]`) from other codegen units. `inline(never)` keeps
            /// the tail a real jump, and the body must visibly consume the whole
            /// window: LLVM deletes a tail call to an empty internal callee, and
            /// with it every computation feeding the window.
            #[inline(never)]
            extern "rust-preserve-none" fn __next<'a, 'b, 'src, 'intern>(
                owner: &'a mut $crate::Owner,
                state: &'b mut $crate::vm::RunState<'src, 'intern>,
                base: *mut $crate::lboxed::LBoxed<'src, 'intern>,
                w0: $crate::lboxed::LBoxed<'src, 'intern>,
                w1: $crate::lboxed::LBoxed<'src, 'intern>,
                w2: $crate::lboxed::LBoxed<'src, 'intern>,
                w3: $crate::lboxed::LBoxed<'src, 'intern>,
                w4: $crate::lboxed::LBoxed<'src, 'intern>,
                w5: $crate::lboxed::LBoxed<'src, 'intern>,
                w6: $crate::lboxed::LBoxed<'src, 'intern>,
                w7: $crate::lboxed::LBoxed<'src, 'intern>,
            ) {
                core::hint::black_box((owner as *mut $crate::Owner, state as *mut _, base, w0, w1, w2, w3, w4, w5, w6, w7));
            }
        }

        impl<$(const $cp: $cpt),*> $crate::window::Window for $name<$($cp),*> {
            fn name(&self) -> &'static str { stringify!($name) }
            fn operands(&self) -> &[usize] { &self.operands }
            fn accesses(&self) -> &'static [$crate::window::Access] { Self::ACCESSES }
            fn captures(&self) -> $crate::window::Captures {
                ::smallvec::smallvec![$($crate::window::Capture::to_bits(self.$cap)),*]
            }
            fn arity(&self) -> usize { Self::ARITY }
            fn stencil(&self, skip: usize) -> usize {
                assert!(skip + Self::ARITY <= $crate::window::WINDOW, "{} at {skip} overruns the window", stringify!($name));
                match skip {
                    0 => Self::__stencil::<0> as *const () as usize,
                    1 => Self::__stencil::<1> as *const () as usize,
                    2 => Self::__stencil::<2> as *const () as usize,
                    3 => Self::__stencil::<3> as *const () as usize,
                    4 => Self::__stencil::<4> as *const () as usize,
                    5 => Self::__stencil::<5> as *const () as usize,
                    6 => Self::__stencil::<6> as *const () as usize,
                    7 => Self::__stencil::<7> as *const () as usize,
                    _ => unreachable!(),
                }
            }
            fn next(&self) -> usize { Self::__next as *const () as usize }
            unsafe fn run<'src, 'intern>(
                &self,
                owner: &mut $crate::Owner,
                state: &mut $crate::vm::RunState<'src, 'intern>,
                base: *mut $crate::lboxed::LBoxed<'src, 'intern>,
                w: &mut $crate::window::Regs<'src, 'intern>,
                skip: usize,
            ) {
                assert!(skip + Self::ARITY <= $crate::window::WINDOW, "{} at {skip} overruns the window", stringify!($name));
                unsafe { Self::__window($(self.$cap,)* owner, state, base, w, skip) }
            }
        }
    };
}
pub(crate) use windowed;

// ---- copy&patch -----------------------------------------------------------

/// Why a stencil can't be copied — the JIT then calls the op's body instead of
/// splatting it — or why copying failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StencilError {
    /// Reading or parsing this executable's own ELF image failed.
    Image(String),
    /// The stencil isn't a function in the symbol table.
    NotInSymtab { op: &'static str },
    /// The stencil doesn't decode (to instructions ending exactly at its end).
    Undecodable { op: &'static str, at: usize },
    /// A RIP displacement isn't where the instruction's layout puts it.
    Displacement { op: &'static str, at: usize },
    /// The stencil has no `become`: no jump to the continuation.
    NoBecome { op: &'static str },
    /// A jump leaves the stencil without being a `become` (e.g. a sibling tail
    /// call), so it would skip the rest of the chain.
    JumpsOut { op: &'static str, at: usize, target: usize },
    /// An indirect jump that isn't a `become` (e.g. through a jump table, whose
    /// entries lead back into the original function).
    IndirectJump { op: &'static str, at: usize },
    /// A reference is out of rel32 range of where the copy landed.
    OutOfRange { target: usize, base: usize },
    /// No executable mapping within rel32 range of the binary.
    Map(String),
}

impl std::fmt::Display for StencilError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Image(e) => write!(f, "can't read this executable's ELF image: {e}"),
            Self::NotInSymtab { op } => write!(f, "{op} stencil isn't in the symbol table"),
            Self::Undecodable { op, at } => write!(f, "{op} stencil doesn't decode at +{at:#x}"),
            Self::Displacement { op, at } => {
                write!(f, "{op} stencil: RIP displacement not where expected at +{at:#x}")
            }
            Self::NoBecome { op } => {
                write!(f, "{op} stencil has no `become` to its continuation")
            }
            Self::JumpsOut { op, at, target } => {
                write!(f, "{op} stencil jumps out to {target:#x} at +{at:#x}")
            }
            Self::IndirectJump { op, at } => {
                write!(f, "{op} stencil has an indirect jump (jump table?) at +{at:#x}")
            }
            Self::OutOfRange { target, base } => {
                write!(f, "{target:#x} is out of rel32 range of the copy at {base:#x}")
            }
            Self::Map(e) => write!(f, "no executable mapping near the binary: {e}"),
        }
    }
}

impl std::error::Error for StencilError {}

/// What the copier needs from this executable's own ELF image: each hole's GOT
/// slot and each function's size (to find the trailing `become`), at runtime
/// addresses.
pub struct Image {
    holes: [Option<usize>; MAX_HOLES],
    sizes: HashMap<usize, usize>,
}

impl Image {
    pub fn load() -> Result<Self, StencilError> {
        let err = |e: &dyn std::fmt::Display| StencilError::Image(e.to_string());
        let bytes = std::fs::read("/proc/self/exe").map_err(|e| err(&e))?;
        let elf = goblin::elf::Elf::parse(&bytes).map_err(|e| err(&e))?;

        let anchor = elf
            .syms
            .iter()
            .find(|s| elf.strtab.get_at(s.st_name) == Some("__lunacy_window_anchor"))
            .ok_or_else(|| err(&"no __lunacy_window_anchor in the symbol table"))?
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
        Ok(Image { holes, sizes })
    }
}

/// A RIP-relative reference in a stencil body: the 4-byte displacement at
/// `field` is measured from the end of its instruction, `end`, and reaches the
/// absolute address `target`. Wherever the body is placed, rewrite the field so
/// it still reaches `target` (or, for a hole, its pool slot).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RipRel {
    pub field: usize,
    pub end: usize,
    pub target: usize,
}

impl RipRel {
    /// Point this reference at `target`, with the body placed at `base`.
    fn patch(&self, code: &mut [u8], base: usize, target: usize) -> Result<(), StencilError> {
        let disp = (target as i64).wrapping_sub((base + self.end) as i64);
        let disp: i32 = disp.try_into().map_err(|_| StencilError::OutOfRange { target, base })?;
        code[self.field..self.field + 4].copy_from_slice(&disp.to_le_bytes());
        Ok(())
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
    /// ...) and relative calls leaving the body. They must keep reaching their
    /// absolute `target` wherever the body is copied; the JIT hands them to
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

/// Copy `op`'s stencil running at `skip`.
///
/// Every exit of a well-formed stencil is its `become`: a tail jump to the op's
/// continuation, which the copy redirects to its end, where the next stencil
/// falls through. When the `become` is the last instruction it is sliced off;
/// otherwise the compiler laid cold code after it (e.g. a panic path, ending in
/// a call that never returns), and the whole body is copied with a trap after it
/// so that nothing can fall off its end. The body is decoded to find every
/// RIP-relative reference: loads of a hole's GOT slot are holes, the rest are
/// relocations. Branches that stay within the body need no fixup (one to the
/// sliced tail becomes a fall-through into the next stencil, as it should). A
/// stencil that can't be copied this way is an error, not a panic, so the JIT
/// can call the op's body instead.
pub unsafe fn stencil_body(image: &Image, op: &dyn Window, skip: usize) -> Result<Body, StencilError> {
    use yaxpeax_arch::LengthedInstruction;
    use yaxpeax_x86::long_mode::{InstDecoder, Instruction, Opcode, Operand, RegSpec};

    let name = op.name();
    let addr = op.stencil(skip);
    let &size = image.sizes.get(&addr).ok_or(StencilError::NotInSymtab { op: name })?;
    let code = unsafe { core::slice::from_raw_parts(addr as *const u8, size) };

    // Decode the whole stencil: (offset, end, instruction).
    let decoder = InstDecoder::default();
    let mut insts: Vec<(usize, usize, Instruction)> = Vec::new();
    let mut off = 0;
    while off < size {
        let inst = decoder
            .decode_slice(&code[off..])
            .map_err(|_| StencilError::Undecodable { op: name, at: off })?;
        let end = off + inst.len().to_const() as usize;
        insts.push((off, end, inst));
        off = end;
    }
    if off != size || insts.is_empty() {
        return Err(StencilError::Undecodable { op: name, at: off });
    }

    // An instruction's RIP-relative memory operand, as (disp field offset,
    // absolute target). The displacement is followed only by the instruction's
    // immediate (if any), so it sits just before it.
    let rip_operand = |off: usize, end: usize, inst: &Instruction| -> Result<Option<(usize, usize)>, StencilError> {
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
        let Some(disp) = disp else { return Ok(None) };
        let field = end - imm_bytes - 4;
        if i32::from_le_bytes(code[field..field + 4].try_into().unwrap()) != disp {
            return Err(StencilError::Displacement { op: name, at: off });
        }
        Ok(Some((field, (addr + end).wrapping_add(disp as isize as usize))))
    };

    // Whether instruction `i` jumps to the continuation. rustc builds with
    // `-Z plt=no`, so depending on whether the continuation is known to be local
    // that's `jmp rel32`, `jmp *[rip+got]`, or `jmp *reg` with `reg` loaded from
    // the GOT slot earlier (LLVM hoists that load above the epilogue). A GOT slot
    // holds the loader-relocated address, so read it to check.
    let next = op.next();
    let got = |slot: usize| unsafe { core::ptr::read_unaligned(slot as *const usize) };
    let jumps_to_next = |i: usize| -> Result<bool, StencilError> {
        let (off, end, inst) = &insts[i];
        if inst.opcode() != Opcode::JMP {
            return Ok(false);
        }
        Ok(match inst.operand(0) {
            Operand::ImmediateI32 { imm } => (addr + end).wrapping_add(imm as isize as usize) == next,
            Operand::Register { reg } => {
                let feeder = insts[..i]
                    .iter()
                    .rev()
                    .take_while(|(_, _, i)| i.opcode() != Opcode::CALL)
                    .find(|(_, _, i)| {
                        i.operand_count() > 0 && matches!(i.operand(0), Operand::Register { reg: r } if r == reg)
                    });
                match feeder {
                    Some((o, e, i)) if i.opcode() == Opcode::MOV => {
                        rip_operand(*o, *e, i)?.is_some_and(|(_, t)| got(t) == next)
                    }
                    _ => false,
                }
            }
            _ => rip_operand(*off, *end, inst)?.is_some_and(|(_, t)| got(t) == next),
        })
    };

    // A final `become` is sliced off; otherwise the whole body is kept.
    let sliced = jumps_to_next(insts.len() - 1)?;
    let kept = if sliced { insts.len() - 1 } else { insts.len() };
    let body_len = if sliced { insts[kept].0 } else { size };

    let mut holes = SmallVec::new();
    let mut relocs = Vec::new();
    let mut nexts = Vec::new();
    for (i, (off, end, inst)) in insts[..kept].iter().enumerate() {
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
                    let rel = RipRel { field: end - 4, end, target };
                    if width == 4 && target == next {
                        // Another `become` (e.g. a duplicated tail).
                        nexts.push(NextRef::Direct(rel));
                    } else if width == 4 && inst.opcode() == Opcode::CALL {
                        relocs.push(rel);
                    } else {
                        // A jump out that isn't a `become` never falls through
                        // to the next stencil (e.g. a sibling tail call).
                        return Err(StencilError::JumpsOut { op: name, at: off, target });
                    }
                }
            }
            // An indirect jump that isn't a `become` (e.g. through a jump table,
            // whose entries lead back into the original function) can't be
            // followed, so the copy would leave the chain.
            _ if inst.opcode() == Opcode::JMP && !jumps_to_next(i)? => {
                return Err(StencilError::IndirectJump { op: name, at: off });
            }
            _ => {}
        }
        // RIP-relative memory operands: a hole's GOT slot, the continuation (its
        // address, or a slot holding it), or anything else.
        if let Some((field, target)) = rip_operand(off, end, inst)? {
            let rel = RipRel { field, end, target };
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
    let mut code = code[..body_len].to_vec();
    if !sliced {
        if nexts.is_empty() {
            return Err(StencilError::NoBecome { op: name });
        }
        code.extend_from_slice(&UD2);
    }
    Ok(Body { code, holes, relocs, nexts })
}

/// `ud2`, which traps: placed after a copied body that doesn't end in its
/// `become`, which must never be reached.
const UD2: [u8; 2] = [0x0f, 0x0b];

/// A buffer of `len` bytes within ±2GiB of this binary, so rel32 references in
/// copied stencils still reach their targets (the same placement the JIT's code
/// buffer uses). The mapping hint is advisory, and another thread can take the
/// gap between reading the maps and mapping, so a buffer placed out of range is
/// retried with a fresh hint.
fn map_near(len: usize) -> Result<MutableBuffer, StencilError> {
    const ATTEMPTS: usize = 8;
    let target = __lunacy_window_anchor as *const () as usize;
    for _ in 0..ATTEMPTS {
        let buf = MutableBuffer::new_with_hint(len, near_hint(len)?).map_err(|e| StencilError::Map(e.to_string()))?;
        if target.abs_diff(buf.as_ptr() as usize) + len < 1 << 31 {
            return Ok(buf);
        }
    }
    Err(StencilError::Map(format!("{ATTEMPTS} mappings placed out of rel32 range")))
}

/// A mapping hint within ±2GiB of this binary with room for `len` bytes.
fn near_hint(len: usize) -> Result<*mut core::ffi::c_void, StencilError> {
    let target = __lunacy_window_anchor as *const () as usize;
    let len = len.next_multiple_of(4096);
    let max = 1usize << 31;
    rsprocmaps::from_path("/proc/self/maps")
        .map_err(|e| StencilError::Map(e.to_string()))?
        .map_windows(|[first, second]| {
            let (Ok(first), Ok(second)) = (first, second) else { return None };
            let start = first.address_range.end as usize;
            let gap = (second.address_range.begin as usize).saturating_sub(start);
            (gap >= len && target.abs_diff(start) + len < max).then_some(start)
        })
        .flatten()
        .next()
        .map(|start| start as *mut _)
        .ok_or_else(|| StencilError::Map("no free gap within rel32 range".into()))
}

/// Copy&patch the stencils of `ops` (each with its `SKIP`) into one executable
/// buffer near the binary: bodies concatenated (so the
/// register window falls through), then `tail`, then the shared pool of hole
/// values. Every hole is repointed at its pool slot, every reference to an op's
/// continuation at that copy's fall-through point (the next stencil), and every
/// other RIP-relative reference is re-targeted at its original absolute address.
pub unsafe fn assemble(
    image: &Image,
    ops: &[(&dyn Window, usize)],
    tail: &[u8],
) -> Result<ExecutableBuffer, StencilError> {
    let mut code = Vec::new();
    let mut holes: Vec<(RipRel, u64)> = Vec::new();
    let mut relocs: Vec<RipRel> = Vec::new();
    // Each continuation reference, with its copy's fall-through offset.
    let mut nexts: Vec<(NextRef, usize)> = Vec::new();
    for &(op, skip) in ops {
        let body = unsafe { stencil_body(image, op, skip) }?;
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

    let map_err = |e: std::io::Error| StencilError::Map(e.to_string());
    let mut buf = map_near(code.len())?;
    buf.set_len(code.len());
    let base = buf.as_mut_ptr() as usize;
    for (i, (r, _)) in holes.iter().enumerate() {
        r.patch(&mut code, base, base + pool + i * 8)?;
    }
    let mut slot = pool + holes.len() * 8;
    for &(n, fall) in &nexts {
        match n {
            NextRef::Direct(r) => r.patch(&mut code, base, base + fall)?,
            NextRef::Indirect(r) => {
                code[slot..slot + 8].copy_from_slice(&((base + fall) as u64).to_le_bytes());
                r.patch(&mut code, base, base + slot)?;
                slot += 8;
            }
        }
    }
    for r in &relocs {
        r.patch(&mut code, base, r.target)?;
    }
    unsafe { core::ptr::copy_nonoverlapping(code.as_ptr(), buf.as_mut_ptr(), code.len()) };
    buf.make_exec().map_err(map_err)
}

/// Call assembled window code (stencil ABI) with the window `w`.
#[cfg(any(test, feature = "check_windows"))]
unsafe fn enter<'src, 'intern>(
    exec: &ExecutableBuffer,
    owner: *mut Owner,
    state: *mut RunState<'src, 'intern>,
    base: *mut LBoxed<'src, 'intern>,
    w: Regs<'src, 'intern>,
) {
    type L<'s, 'i> = LBoxed<'s, 'i>;
    let entry: extern "rust-preserve-none" fn(
        *mut Owner,
        *mut RunState<'src, 'intern>,
        *mut L<'src, 'intern>,
        L<'src, 'intern>, L<'src, 'intern>, L<'src, 'intern>, L<'src, 'intern>,
        L<'src, 'intern>, L<'src, 'intern>, L<'src, 'intern>, L<'src, 'intern>,
    ) = unsafe { core::mem::transmute(exec.ptr(dynasmrt::AssemblyOffset(0))) };
    entry(owner, state, base, w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]);
}

/// Operand slots for an op that reads the whole window (at `SKIP` 0). Its
/// stencil never touches the stack, so the slots are arbitrary.
#[cfg(any(test, feature = "check_windows"))]
fn whole_window() -> [usize; WINDOW] {
    core::array::from_fn(|i| i)
}

/// Differential check (feature `check_windows`): every window op the interpreter
/// runs is also copy&patched and run as native code on the same operands, and
/// the results must match bit for bit. This drives the ops the specializer
/// actually emits — declared at their emit sites, so no test can name them —
/// through the real copier. An op the copier declines is skipped (logged once),
/// just as the JIT leaves it to the interpreter. It re-executes the op, so an
/// op's effects outside its window must be safe to repeat (a table set stores
/// the same value again).
#[cfg(feature = "check_windows")]
mod check {
    use super::*;
    use std::cell::RefCell;

    // Writes the window to the address in its capture (a hole), so observing the
    // result doesn't depend on `base`, which the op under test may use.
    windowed!(CheckFlush, [out: u64], [], |owner, state, base| (w0, w1, w2, w3, w4, w5, w6, w7) {
        let out = out as *mut [u64; WINDOW];
        *out = [w0, w1, w2, w3, w4, w5, w6, w7].map(|w| w.bits());
    });

    struct Checker {
        image: Image,
        out: *mut [u64; WINDOW],
        /// Assembled checks, or `None` for an op the copier declined.
        programs: HashMap<(usize, Captures), Option<ExecutableBuffer>>,
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
                image: Image::load().expect("check_windows: load this executable's image"),
                out: Box::leak(Box::new([0u64; WINDOW])),
                programs: HashMap::new(),
            });
            let flush = CheckFlush::new(c.out as u64, &whole_window());
            let image = &c.image;
            let program = c.programs.entry((op.stencil(0), op.captures())).or_insert_with(|| {
                match unsafe { assemble(image, &[(op, 0), (&flush, 0)], &[0xc3]) } {
                    Ok(exec) => Some(exec),
                    // Debug builds' stencils can keep what optimized ones fold
                    // away (e.g. a jump table for an unfolded `match OP`), but an
                    // optimized stencil the copier rejects is a bug to fix.
                    Err(e) if cfg!(debug_assertions) => {
                        crate::warn!("check_windows: not checked: {e}");
                        None
                    }
                    Err(e) => panic!("check_windows: {e}"),
                }
            });
            let Some(exec) = program else { return };
            unsafe { enter(exec, owner, state, base, before) };
            let native = unsafe { *c.out };
            let interp: [u64; WINDOW] = core::array::from_fn(|i| after[i].bits());
            assert_eq!(native, interp, "{}: copy&patched stencil disagrees with the interpreter", op.name());
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Test-local window ops, declared exactly as an emit site would.
    windowed!(TAdd, [], [], |owner, state, base| (out d, a, b) {
        *d = LBoxed::from_number(a.as_number().unwrap_unchecked() + b.as_number().unwrap_unchecked());
    });
    windowed!(TMul, [], [], |owner, state, base| (out d, a, b) {
        *d = LBoxed::from_number(a.as_number().unwrap_unchecked() * b.as_number().unwrap_unchecked());
    });
    windowed!(TAddK, [k: f64], [], |owner, state, base| (out d, a) {
        *d = LBoxed::from_number(a.as_number().unwrap_unchecked() + k);
    });
    // Flush the whole window to `base[0..WINDOW]`, to observe the result.
    windowed!(Flush, [], [], |owner, state, base| (w0, w1, w2, w3, w4, w5, w6, w7) {
        *(base as *mut [LBoxed; WINDOW]) = [w0, w1, w2, w3, w4, w5, w6, w7];
    });

    // A stencil that calls out of line (as table get/set through `IndexMap`
    // will): the call is a non-hole RIP-relative reference the copier must
    // re-target.
    #[inline(never)]
    extern "C" fn out_of_line(x: f64) -> f64 {
        core::hint::black_box(x * 3.0 + 1.0)
    }
    windowed!(TCall, [], [], |owner, state, base| (out d, a) {
        *d = LBoxed::from_number(out_of_line(a.as_number().unwrap_unchecked()));
    });

    // A branchy stencil: one arm calls out, the other doesn't, which invites the
    // compiler to duplicate the `become` onto each path.
    windowed!(TBranch, [], [], |owner, state, base| (out d, a) {
        let x = a.as_number().unwrap_unchecked();
        if x < 0.0 {
            *d = LBoxed::from_number(out_of_line(x));
        } else {
            *d = LBoxed::from_number(x + 100.0);
        }
    });


    /// Run `exec` on a window starting with `values`, flushed into `out`.
    fn run(exec: &ExecutableBuffer, values: &[f64], out: &mut [LBoxed<'static, 'static>; WINDOW]) {
        let mut w = [LBoxed::NIL; WINDOW];
        for (w, &v) in w.iter_mut().zip(values) {
            *w = LBoxed::from_number(v);
        }
        unsafe { enter(exec, core::ptr::null_mut(), core::ptr::null_mut(), out.as_mut_ptr(), w) };
    }

    /// Both arms of a branchy stencil fall through to the next stencil, however
    /// many `become`s the compiler left in it.
    #[test]
    fn copy_and_patch_branches() {
        let image = Image::load().unwrap();
        let branch = TBranch::new(&[0, 0]);
        let flush = Flush::new(&whole_window());
        let exec = unsafe { assemble(&image, &[(&branch, 0), (&flush, 0)], &[0xc3]) }.unwrap();
        for (x, want) in [(-2.0, -5.0), (2.0, 102.0)] {
            let mut out = [LBoxed::NIL; WINDOW];
            run(&exec, &[0.0, x], &mut out);
            assert_eq!([out[0].as_number(), out[1].as_number()], [Some(want), Some(x)], "input {x}");
        }
    }

    /// The out-of-line call shows up in `relocations()` (directly, or through
    /// the GOT slot it calls through), and the copy still calls it correctly.
    #[test]
    fn copy_and_patch_relocates_calls() {
        let image = Image::load().unwrap();
        let call = TCall::new(&[0, 0]);
        let flush = Flush::new(&whole_window());

        let helper = out_of_line as *const () as usize;
        let body = unsafe { stencil_body(&image, &call, 0) }.unwrap();
        assert!(
            body.relocations().iter().any(|r| r.target == helper
                || unsafe { *(r.target as *const usize) } == helper),
            "call to the helper not among {:x?}",
            body.relocations()
        );

        let exec = unsafe { assemble(&image, &[(&call, 0), (&flush, 0)], &[0xc3]) }.unwrap();
        let mut out = [LBoxed::NIL; WINDOW];
        run(&exec, &[0.0, 2.0], &mut out);
        assert_eq!([out[0].as_number(), out[1].as_number()], [Some(7.0), Some(2.0)]);
    }

    /// Copy&patch a chain shifting along the window, as a stack evaluates
    /// `(w2 + w3) * w2`, and run it on (0, 0, 3, 4, nil..): Add at 1 (w1 = w2 +
    /// w3), Mul at 0 reading that result in place (w0 = w1 * w2), AddK at 2 (w2 =
    /// w3 + 0.5, a capture/hole), then Flush. Inputs are never written.
    #[test]
    fn copy_and_patch_chain() {
        let image = Image::load().unwrap();
        let add = TAdd::new(&[1, 2, 3]);
        let mul = TMul::new(&[0, 1, 2]);
        let addk = TAddK::new(0.5, &[2, 3]);
        let flush = Flush::new(&whole_window());
        let ops: [(&dyn Window, usize); 4] = [(&add, 1), (&mul, 0), (&addk, 2), (&flush, 0)];
        let exec = unsafe { assemble(&image, &ops, &[0xc3]) }.unwrap();

        let mut out = [LBoxed::NIL; WINDOW];
        run(&exec, &[0.0, 0.0, 3.0, 4.0], &mut out);
        let out = out.map(|v| v.as_number());
        assert_eq!(out[..4], [Some(21.0), Some(7.0), Some(4.5), Some(4.0)]);
        assert!(out[4..].iter().all(Option::is_none));
    }

    /// At every `SKIP`, a copied stencil writes only its output: every other
    /// window register, inputs included, keeps its value.
    #[test]
    fn copy_and_patch_preserves_window() {
        let image = Image::load().unwrap();
        let add = TAdd::new(&[0, 1, 2]);
        let flush = Flush::new(&whole_window());
        let values: [f64; WINDOW] = core::array::from_fn(|i| 10.0 + i as f64);
        for skip in 0..=WINDOW - 3 {
            let exec = unsafe { assemble(&image, &[(&add, skip), (&flush, 0)], &[0xc3]) }.unwrap();
            let mut out = [LBoxed::NIL; WINDOW];
            run(&exec, &values, &mut out);
            let mut want = values;
            want[skip] = values[skip + 1] + values[skip + 2];
            assert_eq!(out.map(|v| v.as_number()), want.map(Some), "Add at {skip}");
        }
    }

    #[test]
    #[should_panic(expected = "two outputs write slot 10")]
    fn operands_distinct_outputs() {
        windowed!(TSwap, [], [], |owner, state, base| (a, b, out c, out d) {
            *c = b;
            *d = a;
        });
        TSwap::new(&[10, 11, 10, 10]);
    }
}
