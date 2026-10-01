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
//!   `(state, base)` (the ABI the JIT pins in r12/r13) followed by the
//!   register window as **scalar** `LBoxed` params `w0..w8` (r14, r15, rdi, rsi, rdx, rcx, r8, r9, r11; see
//!   `WINDOW`). The body's `owner` is forged (`crate::forge_owner`): the
//!   token is zero-sized, so passing it would only spend a register.
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
//! 0 build of `NumericRR` hits the latter (`match OP` isn't folded);
//! optimized builds don't. The interpreter tier runs any window op regardless,
//! and the JIT calls the body of an op the copier rejects.

// Note [Register window]
// ~~~~~~~~~~~~~~~~~~~~~~
// A window op's operands are whole `LBoxed` values held in the register window:
// `WINDOW` registers, passed between stencils as the scalar params `w0..w8`. An
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
// it tests the cached register, and both its edges carry the window on.
//
// The interpreter keeps no window between residuals: `ExecWindow` runs the op's
// body on its operands' stack homes (`Window::on_stack`: inputs read from them,
// outputs written to them, no window), so resuming a block at any residual is
// sound.

use std::collections::HashMap;

use dynasmrt::mmap::{ExecutableBuffer, MutableBuffer};
use smallvec::SmallVec;

use crate::lboxed::LBoxed;
use crate::vm::RunState;
use crate::Owner;

/// Number of register-window slots (w0..w8 = r14, r15, rdi, rsi, rdx, rcx, r8, r9, r11).
/// `rust-preserve-none` passes 12 integer arguments in registers, 2 of them the
/// fixed params, but the 12th (rax) can't be a window register: a stencil's
/// `become` may be an indirect jump through the GOT, whose target LLVM loads
/// into rax even when rax carries an argument, and that load stays in the copy.
pub const WINDOW: usize = 9;
/// Number of hole statics available to captures.
pub const MAX_HOLES: usize = 4;
/// The hole past the captures' holes, whose value is the address of the site's
/// record. See Note [Cold stencils].
pub const SITE_HOLE: usize = MAX_HOLES;
// `Captures` and `Regs` use literal lengths: with `generic_const_exprs` on, a named
// const in a trait method signature makes `Window` dyn-incompatible.
/// A window op's hole values.
pub type Captures = SmallVec<[u64; 4]>;
/// The register window's values.
pub type Regs<'src, 'intern> = [LBoxed<'src, 'intern>; 9];
const _: () = assert!(MAX_HOLES == 4 && WINDOW == 9);

// ---- holes / continuation / anchor ---------------------------------------

unsafe extern "C" {
    #[linkage = "extern_weak"]
    static __lunacy_hole0: *const ();
    #[linkage = "extern_weak"]
    static __lunacy_hole1: *const ();
    #[linkage = "extern_weak"]
    static __lunacy_hole2: *const ();
    #[linkage = "extern_weak"]
    static __lunacy_hole3: *const ();
    /// The site hole: the address of the site's record, for its op's cold
    /// stencil. See Note [Cold stencils].
    #[linkage = "extern_weak"]
    static __lunacy_site: *const ();
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
    let mut value = unsafe {
        match I {
            0 => __lunacy_hole0 as u64,
            1 => __lunacy_hole1 as u64,
            2 => __lunacy_hole2 as u64,
            3 => __lunacy_hole3 as u64,
            SITE_HOLE => __lunacy_site as u64,
            _ => unresolved_window_hole__too_many_captures as u64,
        }
    };
    // A value the op takes apart (`(v >> 16) as u16`) could otherwise be loaded a
    // piece at a time from inside the GOT slot, which the copier can't point at
    // the hole: the empty `asm!` wants all of it in a register, so the slot is
    // loaded whole.
    unsafe { core::arch::asm!("/* hole {0} */", inout(reg) value, options(pure, nomem, nostack, preserves_flags)) };
    value
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Access {
    /// The op reads the slot's value.
    Read,
    /// The op only writes the slot.
    Write,
    /// The op reads the slot's value and writes its new one in place, in the
    /// same register.
    Update,
}

impl Access {
    /// Whether the op reads the slot's value.
    pub fn reads(self) -> bool {
        matches!(self, Access::Read | Access::Update)
    }

    /// Whether the op writes the slot.
    pub fn writes(self) -> bool {
        matches!(self, Access::Write | Access::Update)
    }
}

/// Check a window op's operand slots against its operands' accesses: no two
/// outputs write the same slot, and a slot updated in place is no other
/// operand.
#[doc(hidden)]
pub fn check_operands(name: &str, operands: &[usize], accesses: &[Access]) {
    let outputs = || operands.iter().zip(accesses).filter(|(_, a)| a.writes()).map(|(slot, _)| *slot);
    for (i, a) in outputs().enumerate() {
        assert!(outputs().skip(i + 1).all(|b| b != a), "{name}: two outputs write slot {a}");
    }
    for (slot, _) in operands.iter().zip(accesses).filter(|(_, a)| **a == Access::Update) {
        assert_eq!(operands.iter().filter(|s| *s == slot).count(), 1, "{name}: slot {slot} updated in place is another operand too");
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
    /// Address of the op's cold stencil at `skip`, which its stencil at `skip`
    /// jumps to off its hot path, if it has a cold path. See Note [Cold
    /// stencils].
    fn cold(&self, _skip: usize) -> Option<usize> {
        None
    }
    /// Address of a guard op's second continuation, which its stencils jump to
    /// when it passes. See Note [Guard stencils].
    fn pass(&self) -> Option<usize> {
        None
    }
    /// Run the body on the window `w` at `skip`, with the captures from `self`.
    unsafe fn run<'src, 'intern>(
        &self,
        owner: &mut Owner,
        state: &mut RunState<'src, 'intern>,
        base: *mut LBoxed<'src, 'intern>,
        w: &mut Regs<'src, 'intern>,
        skip: usize,
    );
    /// Run the body on the operands' stack homes: inputs read from and outputs
    /// written to them directly, with no window.
    fn on_stack<'src, 'intern>(&self, owner: &mut Owner, state: &mut RunState<'src, 'intern>);
}

impl dyn Window {
    /// Interpreter tier: run the op on its operands' stack homes. See Note
    /// [Register window].
    pub fn interp<'src, 'intern>(&self, owner: &mut Owner, state: &mut RunState<'src, 'intern>) {
        #[cfg(feature = "check_windows")]
        self.interp_checked(owner, state);
        #[cfg(not(feature = "check_windows"))]
        self.on_stack(owner, state);
    }

    /// `interp` through a window, checked against the op's copy&patched stencil
    /// (see `check`).
    #[cfg(feature = "check_windows")]
    fn interp_checked<'src, 'intern>(&self, owner: &mut Owner, state: &mut RunState<'src, 'intern>) {
        let operands = self.operands().iter().zip(self.accesses()).enumerate();
        let mut w = [LBoxed::NIL; WINDOW];
        for (i, (slot, _)) in operands.clone().filter(|(_, (_, a))| a.reads()) {
            w[i] = state.vals[state.base + slot];
        }
        let base = unsafe { state.vals.stack_ptr.as_non_null_ptr().add(state.base).as_ptr() };
        let before = w;
        unsafe { self.run(owner, state, base, &mut w, 0) };
        check::check(self, owner, state, base, before, &w);
        for (i, (slot, _)) in operands.filter(|(_, (_, a))| a.writes()) {
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

/// Bind each capture through a site's record, `I` counting up from 0: the
/// record's `I`th displacement, after its fall-through address, is from the
/// record to the capture's value. See Note [Cold stencils].
#[doc(hidden)]
macro_rules! bind_record {
    ($site:ident, $idx:expr;) => {};
    ($site:ident, $idx:expr; $cap:ident : $cty:ty $(, $rcap:ident : $rcty:ty)*) => {
        let $cap: $cty = unsafe {
            let displacement = *($site.add(1) as *const i32).add($idx);
            <$cty as $crate::window::Capture>::from_bits(*($site as *const u8).offset(displacement as isize).cast::<u64>())
        };
        $crate::window::bind_record!($site, $idx + 1; $($rcap : $rcty),*);
    };
}
#[doc(hidden)]
pub(crate) use bind_record;

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
///
/// A `cold { .. }` block after the body is the op's cold path: the body then
/// evaluates to whether to take it, and the cold block, with the same bindings,
/// runs after it when it does, in a stencil of its own. See Note [Cold
/// stencils].
///
/// `windowed!(guard Name, ...)` declares a dynamic guard's op, whose body
/// evaluates to whether it passes: the op selects 0 when it does, and its
/// stencils jump to a second continuation instead. See Note [Guard stencils].
///
/// `windowed!(frame Name, ...)`, with no operands, declares an op that only
/// runs at `SKIP` 0 into an empty window, and after which the JIT code loads
/// `base` again, if it needs it: its stencil takes only `state`, and passes on
/// only `state`, so every other register is free for it, rather than kept for a
/// window it has none of.
macro_rules! windowed {
    (
        $(#[$meta:meta])*
        frame $name:ident,
        [$($cap:ident : $cty:ty),* $(,)?],
        [$($cp:ident : $cpt:ty),* $(,)?],
        |$owner:ident, $state:ident, $base:ident| ()
        $body:block
    ) => {
        $crate::window::windowed!(@sort
            [frame $(#[$meta])* $name, [$($cap : $cty),*], [$($cp : $cpt),*], |$owner, $state, $base| $body [] []]
            [] [] [] (0usize)
        );
    };
    (
        $(#[$meta:meta])*
        guard $name:ident,
        [$($cap:ident : $cty:ty),* $(,)?],
        [$($cp:ident : $cpt:ty),* $(,)?],
        |$owner:ident, $state:ident, $base:ident| ($($operands:tt)*)
        $body:block
    ) => {
        $crate::window::windowed!(@sort
            [window $(#[$meta])* $name, [$($cap : $cty),*], [$($cp : $cpt),*], |$owner, $state, $base| $body [] [guard]]
            [] [] [] (0usize) $($operands)*
        );
    };
    (
        $(#[$meta:meta])*
        $name:ident,
        [$($cap:ident : $cty:ty),* $(,)?],
        [$($cp:ident : $cpt:ty),* $(,)?],
        |$owner:ident, $state:ident, $base:ident| ($($operands:tt)*)
        $body:block
        $(cold $cold:block)?
    ) => {
        $crate::window::windowed!(@sort
            [window $(#[$meta])* $name, [$($cap : $cty),*], [$($cp : $cpt),*], |$owner, $state, $base| $body [$($cold)?] []]
            [] [] [] (0usize) $($operands)*
        );
    };
    // `code`, if the op is a guard's.
    (@if_guard [] $($code:tt)*) => {};
    (@if_guard [$guard:ident] $($code:tt)*) => {
        $($code)*
    };
    // The body of an op with no cold path, which never takes it; of one with
    // a cold path, whether to take it; of a guard, whether it passes.
    (@run [] $body:block) => {
        { let () = unsafe { $body }; false }
    };
    (@run [] $body:block, $cold:block) => {
        unsafe { $body }
    };
    (@run [$guard:ident] $body:block) => {
        unsafe { $body }
    };
    (@cold_body []) => {
        {}
    };
    (@cold_body [$cold:block]) => {
        $cold
    };
    // `code`, if the op has a cold path.
    (@if_cold [] $($code:tt)*) => {};
    (@if_cold [$cold:block] $($code:tt)*) => {
        $($code)*
    };
    // Sort the operands into inputs and outputs, each with its window offset,
    // and their accesses in window order.
    (@sort $decl:tt [$($in:tt)*] [$($out:tt)*] [$($acc:tt)*] ($i:expr) inout $op:ident $(, $($rest:tt)*)?) => {
        $crate::window::windowed!(@sort $decl [$($in)*] [$($out)* ($op, $i)] [$($acc)* Update] ($i + 1) $($($rest)*)?);
    };
    (@sort $decl:tt [$($in:tt)*] [$($out:tt)*] [$($acc:tt)*] ($i:expr) out $op:ident $(, $($rest:tt)*)?) => {
        $crate::window::windowed!(@sort $decl [$($in)*] [$($out)* ($op, $i)] [$($acc)* Write] ($i + 1) $($($rest)*)?);
    };
    (@sort $decl:tt [$($in:tt)*] [$($out:tt)*] [$($acc:tt)*] ($i:expr) $op:ident $(, $($rest:tt)*)?) => {
        $crate::window::windowed!(@sort $decl [$($in)* ($op, $i)] [$($out)*] [$($acc)* Read] ($i + 1) $($($rest)*)?);
    };
    (@sort
        [$kind:ident $(#[$meta:meta])* $name:ident, [$($cap:ident : $cty:ty),*], [$($cp:ident : $cpt:ty),*], |$owner:ident, $state:ident, $base:ident| $body:block [$($cold:block)?] [$($guard:ident)?]]
        [$(($in:ident, $ii:expr))*] [$(($out:ident, $oi:expr))*] [$($acc:ident)*] ($arity:expr)
    ) => {
        $(#[$meta])*
        #[derive(Debug, Clone)]
        pub struct $name<$(const $cp: $cpt),*> {
            $(pub $cap: $cty,)*
            operands: ::smallvec::SmallVec<[usize; $crate::window::WINDOW]>,
        }

        #[allow(dead_code, unused_variables, unused_mut, unused_assignments, unused_unsafe)]
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

            /// The body, shared by the interpreter and the stencil: whether to
            /// take the cold path, or a guard's whether it passes.
            #[inline(always)]
            unsafe fn __run<'a, 'b, 'src, 'intern>(
                $($cap: $cty,)*
                $owner: &'a mut $crate::Owner,
                $state: &'b mut $crate::vm::RunState<'src, 'intern>,
                $base: *mut $crate::lboxed::LBoxed<'src, 'intern>,
                $($in: $crate::lboxed::LBoxed<'src, 'intern>,)*
                $($out: &mut $crate::lboxed::LBoxed<'src, 'intern>,)*
            ) -> bool {
                $crate::window::windowed!(@run [$($guard)?] $body $(, $cold)?)
            }

            /// The cold path's body, shared by the interpreter and the cold
            /// stencil: empty for an op with no cold path, which never runs it.
            #[inline(always)]
            unsafe fn __run_cold<'a, 'b, 'src, 'intern>(
                $($cap: $cty,)*
                $owner: &'a mut $crate::Owner,
                $state: &'b mut $crate::vm::RunState<'src, 'intern>,
                $base: *mut $crate::lboxed::LBoxed<'src, 'intern>,
                $($in: $crate::lboxed::LBoxed<'src, 'intern>,)*
                $($out: &mut $crate::lboxed::LBoxed<'src, 'intern>,)*
            ) {
                unsafe { $crate::window::windowed!(@cold_body [$($cold)?]) }
            }

            /// Run the cold path's body on the window `w` at `skip`, as
            /// `__window` runs the body.
            #[inline(always)]
            unsafe fn __window_cold<'a, 'b, 'src, 'intern>(
                $($cap: $cty,)*
                owner: &'a mut $crate::Owner,
                state: &'b mut $crate::vm::RunState<'src, 'intern>,
                base: *mut $crate::lboxed::LBoxed<'src, 'intern>,
                w: &mut [$crate::lboxed::LBoxed<'src, 'intern>; $crate::window::WINDOW],
                skip: usize,
            ) {
                $( let $in = w[skip + $ii]; )*
                $( let mut $out = w[skip + $oi]; )*
                unsafe { Self::__run_cold($($cap,)* owner, state, base, $($in,)* $(&mut $out,)*) };
                $( w[skip + $oi] = $out; )*
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
            ) -> bool {
                $( let $in = w[skip + $ii]; )*
                $( let mut $out = w[skip + $oi]; )*
                let taken = unsafe { Self::__run($($cap,)* owner, state, base, $($in,)* $(&mut $out,)*) };
                $( w[skip + $oi] = $out; )*
                taken
            }

            $crate::window::windowed!(@stencil $kind, [$($cap : $cty),*] [$($cold)?] [$($guard)?]);
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
                Self::__stencil_at(skip)
            }
            fn next(&self) -> usize { Self::__next as *const () as usize }
            $crate::window::windowed!(@if_guard [$($guard)?]
                fn pass(&self) -> Option<usize> { Some(Self::__pass as *const () as usize) }
            );
            $crate::window::windowed!(@if_cold [$($cold)?]
                fn cold(&self, skip: usize) -> Option<usize> {
                    assert!(skip + Self::ARITY <= $crate::window::WINDOW, "{} at {skip} overruns the window", stringify!($name));
                    Some(Self::__cold_at(skip))
                }
            );
            unsafe fn run<'src, 'intern>(
                &self,
                owner: &mut $crate::Owner,
                state: &mut $crate::vm::RunState<'src, 'intern>,
                base: *mut $crate::lboxed::LBoxed<'src, 'intern>,
                w: &mut $crate::window::Regs<'src, 'intern>,
                skip: usize,
            ) {
                assert!(skip + Self::ARITY <= $crate::window::WINDOW, "{} at {skip} overruns the window", stringify!($name));
                let taken = unsafe { Self::__window($(self.$cap,)* owner, state, base, w, skip) };
                // A guard selects 0 when it passes. See Note [Guard stencils].
                $crate::window::windowed!(@if_guard [$($guard)?] state.select = (!taken) as usize;);
                // An op with a cold path selects 1 when it takes it, which the cold path
                // may change. See Note [Cold stencils].
                $crate::window::windowed!(@if_cold [$($cold)?]
                    state.select = taken as usize;
                    if taken {
                        unsafe { Self::__window_cold($(self.$cap,)* owner, state, base, w, skip) }
                    }
                );
            }
            fn on_stack<'src, 'intern>(
                &self,
                owner: &mut $crate::Owner,
                state: &mut $crate::vm::RunState<'src, 'intern>,
            ) {
                let at = state.base;
                let base = unsafe { state.vals.stack_ptr.as_non_null_ptr().add(at).as_ptr() };
                $( let $in = state.vals[at + self.operands[$ii]]; )*
                $( let mut $out = state.vals[at + self.operands[$oi]]; )*
                let taken = unsafe { Self::__run($(self.$cap,)* owner, state, base, $($in,)* $(&mut $out,)*) };
                $( state.vals[at + self.operands[$oi]] = $out; )*
                $crate::window::windowed!(@if_guard [$($guard)?] state.select = (!taken) as usize;);
                $crate::window::windowed!(@if_cold [$($cold)?]
                    state.select = taken as usize;
                    if taken {
                        $( let $in = state.vals[at + self.operands[$ii]]; )*
                        $( let mut $out = state.vals[at + self.operands[$oi]]; )*
                        unsafe { Self::__run_cold($(self.$cap,)* owner, state, base, $($in,)* $(&mut $out,)*) };
                        $( state.vals[at + self.operands[$oi]] = $out; )*
                    }
                );
            }
        }
    };
    (@stencil window, [$($cap:ident : $cty:ty),*] [$($cold:block)?] [$($guard:ident)?]) => {
            /// The stencil running at `skip`.
            fn __stencil_at(skip: usize) -> usize {
                match skip {
                    0 => Self::__stencil::<0> as *const () as usize,
                    1 => Self::__stencil::<1> as *const () as usize,
                    2 => Self::__stencil::<2> as *const () as usize,
                    3 => Self::__stencil::<3> as *const () as usize,
                    4 => Self::__stencil::<4> as *const () as usize,
                    5 => Self::__stencil::<5> as *const () as usize,
                    6 => Self::__stencil::<6> as *const () as usize,
                    7 => Self::__stencil::<7> as *const () as usize,
                    8 => Self::__stencil::<8> as *const () as usize,
                    _ => unreachable!(),
                }
            }

            /// The stencil running at `SKIP`.
            pub extern "rust-preserve-none" fn __stencil<'b, 'src, 'intern, const SKIP: usize>(
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
                w8: $crate::lboxed::LBoxed<'src, 'intern>,
            ) {
                if SKIP + Self::ARITY > $crate::window::WINDOW {
                    // Never used: `stencil(skip)` rejects such `skip`.
                    unsafe { core::hint::unreachable_unchecked() }
                }
                let mut w = [w0, w1, w2, w3, w4, w5, w6, w7, w8];
                $crate::window::bind_holes!(0; $($cap : $cty),*);
                // The JIT lends this code the thread's owner. See `crate::forge_owner`.
                let taken = unsafe { Self::__window($($cap,)* $crate::forge_owner(), &mut *state, base, &mut w, SKIP) };
                // The window where it is, into the cold stencil. See Note [Cold stencils].
                $crate::window::windowed!(@if_cold [$($cold)?]
                    if taken {
                        state.cold_site = unsafe { $crate::window::hole::<{ $crate::window::SITE_HOLE }>() } as *const u64;
                        become Self::__cold::<SKIP>(state, base, w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], w[8])
                    }
                );
                // A guard's pass, into its second continuation. See Note [Guard stencils].
                $crate::window::windowed!(@if_guard [$($guard)?]
                    if taken {
                        become Self::__pass(state, base, w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], w[8])
                    }
                );
                become Self::__next(state, base, w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], w[8])
            }

            $crate::window::windowed!(@if_guard [$($guard)?]
                /// A guard's second continuation, as `__next` is its first: the
                /// copier points jumps to it at the guard's pass edge. See Note
                /// [Guard stencils].
                #[inline(never)]
                extern "rust-preserve-none" fn __pass<'b, 'src, 'intern>(
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
                w8: $crate::lboxed::LBoxed<'src, 'intern>,
                ) {
                    // Unlike `__next`'s body, or LLVM merges the two, and the
                    // guard's branch between them with them.
                    core::hint::black_box((state as *mut _, base, w0, w1, w2, w3, w4, w5, w6, w7, w8, 1u8));
                }
            );

            $crate::window::windowed!(@if_cold [$($cold)?]
                /// The cold stencil at `skip`.
                fn __cold_at(skip: usize) -> usize {
                    match skip {
                        0 => Self::__cold::<0> as *const () as usize,
                        1 => Self::__cold::<1> as *const () as usize,
                        2 => Self::__cold::<2> as *const () as usize,
                        3 => Self::__cold::<3> as *const () as usize,
                        4 => Self::__cold::<4> as *const () as usize,
                        5 => Self::__cold::<5> as *const () as usize,
                        6 => Self::__cold::<6> as *const () as usize,
                        7 => Self::__cold::<7> as *const () as usize,
                        8 => Self::__cold::<8> as *const () as usize,
                        _ => unreachable!(),
                    }
                }

                /// The cold stencil at `SKIP`: the cold path of every copy of the
                /// stencil at `SKIP`, which jumps here with the window. Private,
                /// as `__next` is, so the stencil's jump to it is a direct `jmp
                /// rel32`, and never inlined into it, which would copy it. See
                /// Note [Cold stencils].
                #[inline(never)]
                extern "rust-preserve-none" fn __cold<'b, 'src, 'intern, const SKIP: usize>(
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
                w8: $crate::lboxed::LBoxed<'src, 'intern>,
                ) {
                    if SKIP + Self::ARITY > $crate::window::WINDOW {
                        unsafe { core::hint::unreachable_unchecked() }
                    }
                    let mut w = [w0, w1, w2, w3, w4, w5, w6, w7, w8];
                    // The site's record: its fall-through, then where its
                    // captures are.
                    let site = state.cold_site;
                    $crate::window::bind_record!(site, 0; $($cap : $cty),*);
                    unsafe { Self::__window_cold($($cap,)* $crate::forge_owner(), &mut *state, base, &mut w, SKIP) };
                    // SAFETY: the site's fall-through point, in JIT code, where
                    // its copy's window continues, at the stack it jumped from.
                    let fall: extern "rust-preserve-none" fn(
                        &'b mut $crate::vm::RunState<'src, 'intern>,
                        *mut $crate::lboxed::LBoxed<'src, 'intern>,
                        $crate::lboxed::LBoxed<'src, 'intern>, $crate::lboxed::LBoxed<'src, 'intern>, $crate::lboxed::LBoxed<'src, 'intern>,
                        $crate::lboxed::LBoxed<'src, 'intern>, $crate::lboxed::LBoxed<'src, 'intern>, $crate::lboxed::LBoxed<'src, 'intern>,
                        $crate::lboxed::LBoxed<'src, 'intern>, $crate::lboxed::LBoxed<'src, 'intern>, $crate::lboxed::LBoxed<'src, 'intern>,
                    ) = unsafe { core::mem::transmute(*site) };
                    become fall(state, base, w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], w[8])
                }
            );

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
            extern "rust-preserve-none" fn __next<'b, 'src, 'intern>(
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
                w8: $crate::lboxed::LBoxed<'src, 'intern>,
            ) {
                core::hint::black_box((state as *mut _, base, w0, w1, w2, w3, w4, w5, w6, w7, w8));
            }
    };
    (@stencil frame, [$($cap:ident : $cty:ty),*] [] []) => {
            /// The stencil, which only runs at `SKIP` 0.
            fn __stencil_at(skip: usize) -> usize {
                assert_eq!(skip, 0, "a frame op runs at SKIP 0");
                Self::__stencil::<0> as *const () as usize
            }

            /// The stencil, at `SKIP` 0 into an empty window: see `windowed!(frame ..)`.
            pub extern "rust-preserve-none" fn __stencil<'b, 'src, 'intern, const SKIP: usize>(
                state: &'b mut $crate::vm::RunState<'src, 'intern>,
            ) {
                let base = unsafe { state.vals.stack_ptr.as_non_null_ptr().add(state.base).as_ptr() };
                let mut w = [$crate::lboxed::LBoxed::NIL; $crate::window::WINDOW];
                $crate::window::bind_holes!(0; $($cap : $cty),*);
                // The JIT lends this code the thread's owner. See `crate::forge_owner`.
                let _ = unsafe { Self::__window($($cap,)* $crate::forge_owner(), &mut *state, base, &mut w, SKIP) };
                become Self::__next(state)
            }

            /// This op's `become` target, as for a window op's.
            #[inline(never)]
            extern "rust-preserve-none" fn __next<'b, 'src, 'intern>(
                state: &'b mut $crate::vm::RunState<'src, 'intern>,
            ) {
                core::hint::black_box(state as *mut _);
            }
    };
}
pub(crate) use windowed;

// ---- copy&patch -----------------------------------------------------------

/// Why a stencil can't be copied — the JIT then calls the op's body instead of
/// splatting it — or why copying failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StencilError {
    /// This build copies no stencils (debug assertions, or `immediate_jit`).
    Disabled,
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
    /// A load of part of a hole's GOT slot, which the copy can't point at the
    /// hole (see `hole`).
    PartialHole { op: &'static str, at: usize },
    /// A load of the site hole other than a whole register's, which the copy
    /// can't make the record's address (see Note [Cold stencils]).
    SiteLoad { op: &'static str, at: usize },
    /// No executable mapping within rel32 range of the binary.
    Map(String),
}

impl std::fmt::Display for StencilError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Disabled => write!(f, "this build copies no stencils"),
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
            Self::PartialHole { op, at } => {
                write!(f, "{op} stencil loads part of a hole's GOT slot at +{at:#x}")
            }
            Self::SiteLoad { op, at } => {
                write!(f, "{op} stencil loads its site hole other than into a whole register at +{at:#x}")
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
    /// The GOT slot of each hole, the site hole last.
    holes: [Option<usize>; MAX_HOLES + 1],
    sizes: HashMap<usize, usize>,
}

impl Image {
    pub fn load() -> Result<Self, StencilError> {
        let err = |e: &dyn std::fmt::Display| StencilError::Image(e.to_string());
        // Mapped, not read: goblin parses in place, so only the pages of the
        // headers and symbol tables are faulted in, not the debug info.
        let file = std::fs::File::open("/proc/self/exe").map_err(|e| err(&e))?;
        // SAFETY: nothing writes our own executable while it runs.
        let bytes = unsafe { memmap2::Mmap::map(&file) }.map_err(|e| err(&e))?;
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
            "__lunacy_hole2" => Some(2),
            "__lunacy_hole3" => Some(3),
            "__lunacy_site" => Some(SITE_HOLE),
            _ => None,
        };
        let mut holes = [None; MAX_HOLES + 1];
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
    /// copy's fall-through point (`fall`); the JIT relocates them against a
    /// label there.
    pub nexts: Vec<NextRef>,
    /// Where in `code` its `become`s go: its end, or the `add rsp, 8` before
    /// it in a body that restores the stack. See Note [Stencil alignment].
    pub fall: usize,
    /// A guard's jumps to its second continuation, re-targeted at its pass
    /// edge. See Note [Guard stencils].
    pub passes: Vec<RipRel>,
    /// Whether it's copied between `sub rsp, 8` and `add rsp, 8`: a jump out
    /// of its middle must first undo the `sub`. See Note [Stencil alignment].
    pub aligned: bool,
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
pub(crate) const RELATIVE_BRANCHES: [yaxpeax_x86::long_mode::Opcode; 23] = {
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
    // Its cold stencil, which it may jump to. See Note [Cold stencils].
    let cold = op.cold(skip);
    // A guard's second continuation. See Note [Guard stencils].
    let pass = op.pass();
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
    // the GOT slot earlier, maybe into another register first (LLVM hoists that
    // load above the epilogue, and may move it into rax for the jump). A GOT slot
    // holds the loader-relocated address, so read it to check.
    let next = op.next();
    let got = |slot: usize| unsafe { core::ptr::read_unaligned(slot as *const usize) };
    // Where the jump at `i` goes, as far as the body says: a direct jump's
    // target, or the value in the GOT slot an indirect one's target is loaded
    // from.
    let jump_target = |i: usize| -> Result<Option<usize>, StencilError> {
        let (off, end, inst) = &insts[i];
        if inst.opcode() != Opcode::JMP {
            return Ok(None);
        }
        Ok(match inst.operand(0) {
            Operand::ImmediateI32 { imm } => Some((addr + end).wrapping_add(imm as isize as usize)),
            Operand::Register { reg } => {
                // The register's last writer, back through register-to-register
                // moves, is the GOT load.
                let (mut reg, mut before) = (reg, i);
                loop {
                    let feeder = insts[..before]
                        .iter()
                        .enumerate()
                        .rev()
                        .take_while(|(_, (_, _, i))| i.opcode() != Opcode::CALL)
                        .find(|(_, (_, _, i))| {
                            i.operand_count() > 0 && matches!(i.operand(0), Operand::Register { reg: r } if r == reg)
                        });
                    match feeder {
                        Some((j, (o, e, i))) if i.opcode() == Opcode::MOV => match i.operand(1) {
                            Operand::Register { reg: from } => (reg, before) = (from, j),
                            _ => break rip_operand(*o, *e, i)?.map(|(_, t)| got(t)),
                        },
                        _ => break None,
                    }
                }
            }
            _ => rip_operand(*off, *end, inst)?.map(|(_, t)| got(t)),
        })
    };
    let jumps_to_next = |i: usize| -> Result<bool, StencilError> { Ok(jump_target(i)? == Some(next)) };

    // A guard's body ending `jcc __next; jmp __pass` is copied ending `j!cc
    // __pass`, falling through to its `become` (see Note [Guard stencils]):
    // the index of that `jcc`, a two-byte `0F 8x` with a rel32.
    let last = insts.len() - 1;
    let inverted = (last > 0 && pass.is_some() && jump_target(last)? == pass).then_some(last - 1).filter(|&i| {
        let (off, end, inst) = &insts[i];
        inst.opcode() != Opcode::JMP
            && RELATIVE_BRANCHES.contains(&inst.opcode())
            && end - off == 6
            && code[*off] == 0x0f
            && code[off + 1] & 0xf0 == 0x80
            && matches!(inst.operand(0), Operand::ImmediateI32 { imm } if (addr + end).wrapping_add(imm as isize as usize) == next)
    });

    // A final `become` is sliced off, and a guard's final jump to `__pass` it
    // inverts into its `jcc`; otherwise the whole body is kept.
    let sliced = inverted.is_some() || jumps_to_next(last)?;
    let kept = if sliced { insts.len() - 1 } else { insts.len() };
    let body_len = if sliced { insts[kept].0 } else { size };

    let mut holes: SmallVec<[(RipRel, usize); MAX_HOLES]> = SmallVec::new();
    let mut relocs: Vec<RipRel> = Vec::new();
    let mut nexts: Vec<NextRef> = Vec::new();
    // Whether it jumps to its cold stencil, directly.
    let mut jumps_cold = false;
    let mut passes: Vec<RipRel> = Vec::new();
    // The opcode bytes of its site hole loads, to make `lea`s.
    let mut leas: SmallVec<[usize; 1]> = SmallVec::new();
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
                    if Some(i) == inverted {
                        passes.push(rel);
                    } else if width == 4 && target == next {
                        // Another `become` (e.g. a duplicated tail).
                        nexts.push(NextRef::Direct(rel));
                    } else if width == 4 && Some(target) == pass && inst.opcode() != Opcode::CALL {
                        passes.push(rel);
                    } else if width == 4 && Some(target) == cold && inst.opcode() != Opcode::CALL {
                        // Out to the cold stencil, which isn't copied.
                        jumps_cold = true;
                        relocs.push(rel);
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
                if i == SITE_HOLE {
                    // `mov r64, [rip+slot]` (REX.W 8B /r), made `lea r64,
                    // [rip+record]` (REX.W 8D /r). See Note [Cold stencils].
                    let whole = inst.opcode() == Opcode::MOV
                        && matches!(inst.operand(0), Operand::Register { reg } if reg.width() == 8)
                        && field >= 3
                        && code[field - 2] == 0x8b
                        && code[field - 3] & 0xf8 == 0x48;
                    if !whole {
                        return Err(StencilError::SiteLoad { op: name, at: off });
                    }
                    leas.push(field - 2);
                }
                holes.push((rel, i));
            } else if image.holes.iter().flatten().any(|&slot| slot < target && target < slot + 8) {
                return Err(StencilError::PartialHole { op: name, at: off });
            } else if inst.opcode() == Opcode::LEA && target == next {
                nexts.push(NextRef::Direct(rel));
            } else if inst.opcode() != Opcode::LEA && got(target) == next {
                nexts.push(NextRef::Indirect(rel));
            } else {
                relocs.push(rel);
            }
        }
    }
    if !sliced && nexts.is_empty() {
        return Err(StencilError::NoBecome { op: name });
    }
    // Between `sub rsp, 8` and `add rsp, 8` if it uses the stack, or jumps to
    // a cold stencil that does, which starts where it jumps from. See Notes
    // [Stencil alignment] and [Cold stencils].
    let cold_uses_stack = match cold {
        Some(cold) if jumps_cold => unsafe { stencil_uses_stack(image, cold, name)? },
        _ => false,
    };
    let aligned = cold_uses_stack || insts[..kept].iter().any(|(_, _, inst)| uses_stack(inst));
    let prefix: &[u8] = if aligned { &SUB_RSP_8 } else { &[] };
    let shift = |r: RipRel| RipRel { field: r.field + prefix.len(), end: r.end + prefix.len(), ..r };
    let holes = holes.into_iter().map(|(r, i)| (shift(r), i)).collect();
    let relocs = relocs.into_iter().map(shift).collect();
    let passes = passes.into_iter().map(shift).collect();
    let nexts = nexts
        .into_iter()
        .map(|n| match n {
            NextRef::Direct(r) => NextRef::Direct(shift(r)),
            NextRef::Indirect(r) => NextRef::Indirect(shift(r)),
        })
        .collect();
    let mut copy = prefix.to_vec();
    copy.extend_from_slice(&code[..body_len]);
    for at in leas {
        copy[prefix.len() + at] = 0x8d;
    }
    if let Some(i) = inverted {
        copy[prefix.len() + insts[i].0 + 1] ^= 1;
    }
    if !sliced {
        copy.extend_from_slice(&UD2);
    }
    let fall = copy.len();
    if aligned {
        copy.extend_from_slice(&ADD_RSP_8);
    }
    Ok(Body { code: copy, holes, relocs, nexts, fall, passes, aligned })
}

/// Whether the stencil at `addr` uses the stack anywhere (`uses_stack`).
unsafe fn stencil_uses_stack(image: &Image, addr: usize, op: &'static str) -> Result<bool, StencilError> {
    use yaxpeax_arch::LengthedInstruction;
    use yaxpeax_x86::long_mode::InstDecoder;
    let &size = image.sizes.get(&addr).ok_or(StencilError::NotInSymtab { op })?;
    let code = unsafe { core::slice::from_raw_parts(addr as *const u8, size) };
    let decoder = InstDecoder::default();
    let mut off = 0;
    while off < size {
        let inst = decoder.decode_slice(&code[off..]).map_err(|_| StencilError::Undecodable { op, at: off })?;
        if uses_stack(&inst) {
            return Ok(true);
        }
        off += inst.len().to_const() as usize;
    }
    Ok(false)
}

/// `ud2`, which traps: placed after a copied body that doesn't end in its
/// `become`, which must never be reached.
const UD2: [u8; 2] = [0x0f, 0x0b];

// Note [Cold stencils]
// ~~~~~~~~~~~~~~~~~~~~
// A window op with a cold path (`windowed!`'s `cold` block) has a second
// stencil per `SKIP`, `__cold::<SKIP>`, with the same parameters: its stencil
// ends its hot path in a tail jump to it, with the window where it was, so the
// hot path needs no call, and so saves nothing around one and moves no
// arguments into place.
//
// The cold stencil isn't copied: every copy of the op at that `SKIP` shares the
// one in this executable, and reaches it with a jump relocated like a call.
// What differs between copies, their captures and where each continues, is the
// site's record, `[fall-through address, displacement to each capture's value
// (i32)...]`, which the JIT lays in the region's pool, whose values the copy
// loads its captures from too: before the jump, the copy stores the record's address,
// its site hole (`SITE_HOLE`), to `RunState::cold_site` (`become` wants the
// callee's signature to be the caller's, so it can't be an argument). The cold
// stencil binds the captures from the record, runs the cold block, and ends
// in a tail jump to the record's fall-through address, the window where the
// cold block left it.
//
// A site costs its record, and no more of the pool: its capture values are
// the pool's, shared with every copy capturing the same, and its load of the
// site hole, a `mov` from the hole's slot, is copied as an `lea` of the record
// itself, so no slot holds the record's address.
//
// The cold stencil starts where its copy jumped from, so at the copied body's
// stack: a body that jumps to a cold stencil that uses the stack (for a call
// out of line, or an aligned spill) is copied between `sub rsp, 8` and `add
// rsp, 8` (Note [Stencil alignment]), which leaves the stack as a call would,
// and its fall-through point is the `add rsp, 8`. One whose cold stencil
// doesn't use the stack needs neither.
//
// Run by the interpreter, an op with a cold path selects 1 if it takes it and 0
// if not, which its cold path may change; its stencils select nothing they don't
// themselves, as JIT code taking the way on after an optimistic op needs no
// `select` (Note [Optimistic ops] in `specialize`).

// Note [Guard stencils]
// ~~~~~~~~~~~~~~~~~~~~~
// A dynamic guard's op (`windowed!(guard ..)`) has a body that evaluates to
// whether the guard passes. Run by the interpreter, the op selects 0 when it
// does. Its stencils instead end in a second continuation, `__pass`, when it
// does, and in `__next` when it doesn't: the choice is a branch on what the
// body computed, and the copy's jump to `__pass` goes straight to the guard's
// pass edge, rather than the JIT code testing `select` in memory after it,
// which nothing then writes. A body ending `jcc __next; jmp __pass` is copied
// ending in the inverted `jcc` to the pass edge, falling through where its
// `become` would go. A copy between `sub rsp, 8` and `add rsp, 8` jumps to its
// pass edge through an `add rsp, 8` of its own (Note [Stencil alignment]).

// Note [Stencil alignment]
// ~~~~~~~~~~~~~~~~~~~~~~~~
// A stencil is compiled as a function, so its code assumes it was called: the
// stack is 8 past 16-aligned when it starts, a return address below it, and
// its own pushes and stack adjustments align it from there for the calls it
// makes (a cold path's out-of-line helper) and its aligned spills. Copied into
// JIT code, it starts where the stack is 16-aligned, and no call pushes a
// return address. So a body that uses the stack (`uses_stack`: it names `rsp`,
// or pushes, pops or calls) is copied between `sub rsp, 8` and `add rsp, 8`,
// which recreate the alignment it assumes; its `become`s go to the `add rsp, 8`
// (`Body::fall`). A body that doesn't use the stack doesn't depend on its
// alignment, and is copied as it is.

/// `sub rsp, 8` and `add rsp, 8`, around a body that uses the stack. See Note
/// [Stencil alignment].
const SUB_RSP_8: [u8; 4] = [0x48, 0x83, 0xec, 0x08];
const ADD_RSP_8: [u8; 4] = [0x48, 0x83, 0xc4, 0x08];

/// Whether `inst` uses the stack: names `rsp` (as a register or a memory
/// operand's base, as it can't be an index), or pushes, pops or calls. See Note
/// [Stencil alignment].
fn uses_stack(inst: &yaxpeax_x86::long_mode::Instruction) -> bool {
    use yaxpeax_x86::long_mode::{Opcode::*, Operand, RegSpec};
    if matches!(inst.opcode(), PUSH | POP | PUSHF | POPF | CALL | CALLF | ENTER | LEAVE | RETURN | RETF | IRET) {
        return true;
    }
    let sp = |r: RegSpec| [RegSpec::rsp(), RegSpec::esp(), RegSpec::sp(), RegSpec::spl()].contains(&r);
    (0..inst.operand_count()).any(|i| match inst.operand(i) {
        Operand::Register { reg } => sp(reg),
        Operand::MemDeref { base }
        | Operand::Disp { base, .. }
        | Operand::MemBaseIndexScale { base, .. }
        | Operand::MemBaseIndexScaleDisp { base, .. }
        | Operand::MemDerefMasked { base, .. }
        | Operand::DispMasked { base, .. }
        | Operand::MemBaseIndexScaleMasked { base, .. }
        | Operand::MemBaseIndexScaleDispMasked { base, .. } => sp(base),
        _ => false,
    })
}

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
    // Each site's record's fall-through offset and captures, and each site
    // hole's `lea` of its record. See Note [Cold stencils].
    let mut records: Vec<(usize, Captures)> = Vec::new();
    let mut record_refs: Vec<(RipRel, usize)> = Vec::new();
    for &(op, skip) in ops {
        let body = unsafe { stencil_body(image, op, skip) }?;
        let captures = op.captures();
        let at = code.len();
        let shift = |r: RipRel| RipRel { field: r.field + at, end: r.end + at, ..r };
        code.extend_from_slice(&body.code);
        let fall = at + body.fall;
        for &(r, i) in &body.holes {
            match i {
                SITE_HOLE => record_refs.push((shift(r), records.len())),
                i => holes.push((shift(r), captures[i])),
            }
        }
        if body.holes.iter().any(|&(_, i)| i == SITE_HOLE) {
            records.push((fall, captures));
        }
        relocs.extend(body.relocs.iter().map(|&r| shift(r)));
        nexts.extend(body.nexts.iter().map(|n| match *n {
            NextRef::Direct(r) => (NextRef::Direct(shift(r)), fall),
            NextRef::Indirect(r) => (NextRef::Indirect(shift(r)), fall),
        }));
        // Either way a guard goes, the checked code continues.
        nexts.extend(body.passes.iter().map(|&r| (NextRef::Direct(shift(r)), fall)));
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
    // Then the records, each followed by its captures' values.
    let mut record_at = Vec::with_capacity(records.len());
    for (_, captures) in &records {
        record_at.push(code.len());
        let displacements = (4 * captures.len()).next_multiple_of(8);
        code.resize(code.len() + 8 + displacements + 8 * captures.len(), 0);
    }

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
    for ((fall, captures), &at) in records.iter().zip(&record_at) {
        code[at..at + 8].copy_from_slice(&((base + fall) as u64).to_le_bytes());
        let values = at + 8 + (4 * captures.len()).next_multiple_of(8);
        for (i, value) in captures.iter().enumerate() {
            let slot = values + 8 * i;
            code[slot..slot + 8].copy_from_slice(&value.to_le_bytes());
            let displacement = i32::try_from(slot - at).unwrap();
            code[at + 8 + 4 * i..at + 12 + 4 * i].copy_from_slice(&displacement.to_le_bytes());
        }
    }
    for &(r, record) in &record_refs {
        r.patch(&mut code, base, base + record_at[record])?;
    }
    unsafe { core::ptr::copy_nonoverlapping(code.as_ptr(), buf.as_mut_ptr(), code.len()) };
    buf.make_exec().map_err(map_err)
}

/// Call assembled window code (stencil ABI) with the window `w`.
#[cfg(any(test, feature = "check_windows"))]
unsafe fn enter<'src, 'intern>(
    exec: &ExecutableBuffer,
    state: *mut RunState<'src, 'intern>,
    base: *mut LBoxed<'src, 'intern>,
    w: Regs<'src, 'intern>,
) {
    type L<'s, 'i> = LBoxed<'s, 'i>;
    let entry: extern "rust-preserve-none" fn(
        *mut RunState<'src, 'intern>,
        *mut L<'src, 'intern>,
        L<'src, 'intern>, L<'src, 'intern>, L<'src, 'intern>, L<'src, 'intern>,
        L<'src, 'intern>, L<'src, 'intern>, L<'src, 'intern>, L<'src, 'intern>,
        L<'src, 'intern>,
    ) = unsafe { core::mem::transmute(exec.ptr(dynasmrt::AssemblyOffset(0))) };
    entry(state, base, w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], w[8]);
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
    windowed!(CheckFlush, [out: u64], [], |owner, state, base| (w0, w1, w2, w3, w4, w5, w6, w7, w8) {
        let out = out as *mut [u64; WINDOW];
        *out = [w0, w1, w2, w3, w4, w5, w6, w7, w8].map(|w| w.bits());
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
            unsafe { enter(exec, state, base, before) };
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
        *d = LBoxed::from_number(crate::unchecked_unwrap(a.as_number()) + crate::unchecked_unwrap(b.as_number()));
    });
    windowed!(TMul, [], [], |owner, state, base| (out d, a, b) {
        *d = LBoxed::from_number(crate::unchecked_unwrap(a.as_number()) * crate::unchecked_unwrap(b.as_number()));
    });
    windowed!(TAddK, [k: f64], [], |owner, state, base| (out d, a) {
        *d = LBoxed::from_number(crate::unchecked_unwrap(a.as_number()) + k);
    });
    // Flush the whole window to `base[0..WINDOW]`, to observe the result.
    windowed!(Flush, [], [], |owner, state, base| (w0, w1, w2, w3, w4, w5, w6, w7, w8) {
        *(base as *mut [LBoxed; WINDOW]) = [w0, w1, w2, w3, w4, w5, w6, w7, w8];
    });

    // A stencil that calls out of line (as table get/set through `IndexMap`
    // will): the call is a non-hole RIP-relative reference the copier must
    // re-target.
    #[inline(never)]
    extern "C" fn out_of_line(x: f64) -> f64 {
        core::hint::black_box(x * 3.0 + 1.0)
    }
    windowed!(TCall, [], [], |owner, state, base| (out d, a) {
        *d = LBoxed::from_number(out_of_line(crate::unchecked_unwrap(a.as_number())));
    });

    // A branchy stencil: one arm calls out, the other doesn't, which invites the
    // compiler to duplicate the `become` onto each path.
    windowed!(TBranch, [], [], |owner, state, base| (out d, a) {
        let x = crate::unchecked_unwrap(a.as_number());
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
        unsafe { enter(exec, core::ptr::null_mut(), out.as_mut_ptr(), w) };
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
                || unsafe { (r.target as *const usize).read_unaligned() } == helper),
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
