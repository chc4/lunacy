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
//! For the JIT to splat a stencil, its body must be copy&patch-safe: no
//! RIP-relative references other than holes (no panic paths, no calls to
//! non-inlined functions), and it must be built optimized (debug builds add
//! precondition-check calls); see `just test-stencils`. The interpreter tier runs
//! any window op regardless.

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

/// What the copier needs from this executable's own ELF: each hole's GOT slot
/// and each function's size (to assert the trailing `become`), at runtime
/// addresses.
pub struct Relocs {
    holes: [Option<u64>; MAX_HOLES],
    sizes: HashMap<u64, u64>,
}

impl Relocs {
    pub fn load() -> Self {
        let bytes = std::fs::read("/proc/self/exe").expect("read own executable");
        let elf = goblin::elf::Elf::parse(&bytes).expect("parse own ELF");

        let anchor = elf
            .syms
            .iter()
            .find(|s| elf.strtab.get_at(s.st_name) == Some("__lunacy_window_anchor"))
            .expect("window anchor in symtab")
            .st_value;
        let bias = (__lunacy_window_anchor as *const () as u64).wrapping_sub(anchor);

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
                holes[i] = Some(bias.wrapping_add(r.r_offset));
            }
        }

        let sizes = elf
            .syms
            .iter()
            .filter(|s| s.is_function() && s.st_size != 0)
            .map(|s| (bias.wrapping_add(s.st_value), s.st_size))
            .collect();
        Relocs { holes, sizes }
    }
}

/// A stencil's code with its trailing `become` sliced off, and the disp32 offset
/// of each hole load in it (tagged with the hole index).
pub struct Body {
    pub code: Vec<u8>,
    pub holes: SmallVec<[(usize, usize); MAX_HOLES]>,
}

/// Copy `op`'s stencil at window offset `k`. Asserts its last instruction is the
/// `become` jmp to the op's continuation (slicing it for fall-through is only
/// valid then) and finds its hole loads by matching each disp32's RIP target
/// against a hole's GOT slot.
pub unsafe fn stencil_body(relocs: &Relocs, op: &dyn Window, k: usize) -> Body {
    let addr = op.stencil(k);
    let size = *relocs.sizes.get(&(addr as u64)).expect("stencil in symtab") as usize;
    let code = unsafe { core::slice::from_raw_parts(addr as *const u8, size) };
    let next = op.next();
    // The RIP-relative target of a disp32 ending at `end` (exclusive).
    let rip_target = |end: usize| {
        let disp = i32::from_le_bytes(code[end - 4..end].try_into().unwrap());
        addr.wrapping_add(end).wrapping_add(disp as isize as usize)
    };
    // The `become` must be the stencil's last instruction(s), jumping to this
    // op's continuation. rustc builds with `-Z plt=no`, so depending on whether
    // the continuation is known to be local, the tail is one of:
    //   e9 rel32                           jmp next
    //   ff 25 disp32                       jmp *[rip+got]
    //   48 8b 05 disp32 ; ff e0            mov rax, [rip+got] ; jmp *rax
    // (a GOT slot holds the loader-relocated address, so read it to check).
    let got = |slot: usize| unsafe { *(slot as *const usize) };
    let body_len = if size >= 5 && code[size - 5] == 0xe9 && rip_target(size) == next {
        size - 5
    } else if size >= 6 && code[size - 6..size - 4] == [0xff, 0x25] && got(rip_target(size)) == next {
        size - 6
    } else if size >= 9
        && code[size - 9..size - 6] == [0x48, 0x8b, 0x05]
        && code[size - 2..] == [0xff, 0xe0]
        && got(rip_target(size - 2)) == next
    {
        size - 9
    } else {
        panic!("{} stencil at offset {k} does not end in `become` to its continuation", op.name());
    };
    let code = code[..body_len].to_vec();

    let mut holes = SmallVec::new();
    let mut p = 0;
    while p + 4 <= code.len() {
        let disp = i32::from_le_bytes(code[p..p + 4].try_into().unwrap());
        let target = (addr as u64).wrapping_add((p + 4) as u64).wrapping_add(disp as i64 as u64);
        if let Some(i) = relocs.holes.iter().position(|h| *h == Some(target)) {
            holes.push((p, i));
            p += 4;
        } else {
            p += 1;
        }
    }
    Body { code, holes }
}

/// Copy&patch `ops` — each a window op and the window offset its operands sit
/// at — into one executable buffer: bodies concatenated (so the register window
/// falls through), then `tail`, then the shared hole-value pool every hole load
/// is repointed at.
pub unsafe fn assemble(relocs: &Relocs, ops: &[(&dyn Window, usize)], tail: &[u8]) -> ExecutableBuffer {
    let mut code = Vec::new();
    let mut patches: Vec<(usize, u64)> = Vec::new();
    for &(op, k) in ops {
        let body = unsafe { stencil_body(relocs, op, k) };
        let captures = op.captures();
        let base = code.len();
        code.extend_from_slice(&body.code);
        for &(off, i) in &body.holes {
            patches.push((base + off, captures[i]));
        }
    }
    code.extend_from_slice(tail);

    while code.len() % 8 != 0 {
        code.push(0x90);
    }
    let pool = code.len();
    for (i, &(disp_off, val)) in patches.iter().enumerate() {
        let slot = pool + i * 8;
        code.extend_from_slice(&val.to_le_bytes());
        let disp = slot as i64 - (disp_off as i64 + 4);
        code[disp_off..disp_off + 4].copy_from_slice(&(disp as i32).to_le_bytes());
    }

    let mut buf = MutableBuffer::new(code.len()).unwrap();
    buf.set_len(code.len());
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
        relocs: Relocs,
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
                relocs: Relocs::load(),
                out: Box::leak(Box::new([0u64; WINDOW])),
                programs: HashMap::new(),
            });
            let flush = CheckFlush::new(c.out as u64, &[0; WINDOW], &[None; WINDOW]);
            let relocs = &c.relocs;
            let exec = c
                .programs
                .entry((op.stencil(0), op.captures()))
                .or_insert_with(|| unsafe { assemble(relocs, &[(op, 0), (&flush, 0)], &[0xc3]) });
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

    /// Copy&patch a chain over the register window and run it: prepare
    /// (a, b, c), Add at offset 1 (b+c), Mul at offset 0 (a*prev), AddK at offset
    /// 0 (a capture/hole), then Flush.
    #[test]
    #[cfg_attr(debug_assertions, ignore = "stencils must be built optimized: run `just test-stencils`")]
    fn copy_and_patch_chain() {
        let relocs = Relocs::load();
        let add = TAdd::new(&[0, 0], &[None, None]);
        let mul = TMul::new(&[0, 0], &[None, None]);
        let addk = TAddK::new(0.5, &[0], &[None]);
        let flush = Flush::new(&[0; 4], &[None; 4]);
        let ops: [(&dyn Window, usize); 4] = [(&add, 1), (&mul, 0), (&addk, 0), (&flush, 0)];
        let exec = unsafe { assemble(&relocs, &ops, &[0xc3]) };
        // Same ABI as a stencil, with the (unused here) owner/state as raw words.
        let entry: extern "rust-preserve-none" fn(
            usize,
            usize,
            *mut LBoxed<'static, 'static>,
            LBoxed<'static, 'static>,
            LBoxed<'static, 'static>,
            LBoxed<'static, 'static>,
            LBoxed<'static, 'static>,
        ) = unsafe { core::mem::transmute(exec.ptr(AssemblyOffset(0))) };

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
