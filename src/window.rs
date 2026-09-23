//! Copy&patch register-window stencils. See `docs/jit-register-cache.md` and the
//! `src/bin/windowed.rs` proof of concept this is ported from.
//!
//! A window op is declared once with [`windowed!`]. That produces:
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
//!   operands are `w[K..K+ARITY]`. The stencil ends in `become __next(..)`, which
//!   the copier slices off so the window falls through into the next stencil.
//!
//! Captures reach the stencil through `extern_weak` hole statics (`__lunacy_holeN`).
//! Under plain PIE each read is a RIP-relative load from the hole's GOT slot; the
//! copier finds those loads via this executable's own dynamic relocations (goblin)
//! and repoints them at a shared value pool laid after the code. The interpreter
//! tier cannot run the stencil itself (its holes read 0 until patched), so it runs
//! the same body with captures from the struct: load the operand slots, run,
//! flush.
//!
//! Stencil bodies must be copy&patch-safe: no RIP-relative references other than
//! holes (so no panics, no calls to non-inlined functions — e.g. libm `fmod`/`pow`,
//! which is why MOD/POW aren't window ops yet), and the stencil must be built
//! optimized (debug builds add precondition-check calls); see `just test-stencils`.

use std::collections::HashMap;

use dynasmrt::mmap::{ExecutableBuffer, MutableBuffer};
use smallvec::{smallvec, SmallVec};

use crate::lboxed::LBoxed;
use crate::vm::{Opcode, RunState};
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
}

/// Read hole `i`. Only called with a constant index from a stencil, so after
/// inlining it folds to a single RIP-relative load of that hole's GOT slot.
#[inline(always)]
unsafe fn hole(i: usize) -> u64 {
    unsafe {
        match i {
            0 => __lunacy_hole0 as u64,
            1 => __lunacy_hole1 as u64,
            _ => core::hint::unreachable_unchecked(),
        }
    }
}

/// Stable symbol for recovering the PIE load bias (runtime address vs ELF vaddr).
#[unsafe(no_mangle)]
pub extern "C" fn __lunacy_window_anchor() {}

/// The `become` continuation every stencil ends in. Weak so the stencils link;
/// the `jmp` to it is sliced off when copying, so this body never runs.
#[linkage = "weak"]
pub extern "rust-preserve-none" fn __next<'a, 'b, 'src, 'intern>(
    _owner: &'a mut Owner,
    _state: &'b mut RunState<'src, 'intern>,
    _base: *mut LBoxed<'src, 'intern>,
    _w0: LBoxed<'src, 'intern>,
    _w1: LBoxed<'src, 'intern>,
    _w2: LBoxed<'src, 'intern>,
    _w3: LBoxed<'src, 'intern>,
) {
}

fn next_addr() -> usize {
    __next as *const () as usize
}

// ---- captures -------------------------------------------------------------

/// A value that can live in a hole: plain bits, no lifetimes (the window structs
/// are `'static`).
pub trait Capture: Copy + std::fmt::Debug {
    fn to_bits(self) -> u64;
    unsafe fn from_bits(bits: u64) -> Self;
}

impl Capture for f64 {
    fn to_bits(self) -> u64 {
        f64::to_bits(self)
    }
    unsafe fn from_bits(bits: u64) -> Self {
        f64::from_bits(bits)
    }
}

impl Capture for u64 {
    fn to_bits(self) -> u64 {
        self
    }
    unsafe fn from_bits(bits: u64) -> Self {
        bits
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
    /// Run the body on `ops` (this op's operands, in order) with the captures
    /// from `self`.
    unsafe fn run<'src, 'intern>(
        &self,
        owner: &mut Owner,
        state: &mut RunState<'src, 'intern>,
        base: *mut LBoxed<'src, 'intern>,
        ops: *mut LBoxed<'src, 'intern>,
    );

    /// Interpreter tier: retrieve the operand slots, run the body, flush.
    fn interp<'src, 'intern>(&self, owner: &mut Owner, state: &mut RunState<'src, 'intern>) {
        let mut w = [LBoxed::NIL; WINDOW];
        for (i, &s) in self.loads().iter().enumerate() {
            w[i] = state.vals[state.base + s as usize];
        }
        let base = unsafe { state.vals.stack_ptr.as_non_null_ptr().add(state.base).as_ptr() };
        unsafe { self.run(owner, state, base, w.as_mut_ptr()) };
        for (i, s) in self.stores().iter().enumerate() {
            if let Some(s) = s {
                state.vals[state.base + *s as usize] = w[i];
            }
        }
    }
}

macro_rules! count_idents {
    () => { 0usize };
    ($h:ident $($t:ident)*) => { 1usize + count_idents!($($t)*) };
}

/// Declare a window op:
///
/// ```ignore
/// windowed! {
///     pub NumAddK [k: f64] (owner, state, base) (a) {
///         *a = LBoxed::from_number(num(*a) + k);
///     }
/// }
/// ```
///
/// `[captures]` become struct fields / holes (at most `MAX_HOLES`, lifetime-free
/// [`Capture`] types). `(owner, state, base)` names the fixed params. `(a, ...)`
/// are the window operands, bound in the body as `&mut LBoxed`.
macro_rules! windowed {
    (
        $(#[$meta:meta])*
        $vis:vis $name:ident [$($cap:ident : $cty:ty),* $(,)?]
        ($owner:ident, $state:ident, $base:ident)
        ($($op:ident),+ $(,)?)
        $body:block
    ) => {
        $(#[$meta])*
        #[derive(Debug, Clone)]
        $vis struct $name {
            $(pub $cap: $cty,)*
            /// Stack slot each window operand is loaded from, in window order.
            pub loads: SmallVec<[u16; WINDOW]>,
            /// Stack slot each window operand is flushed to after the op.
            pub stores: SmallVec<[Option<u16>; WINDOW]>,
        }

        #[allow(unused_variables, unused_mut, unused_assignments, unused_unsafe, unused_comparisons, clippy::too_many_arguments)]
        impl $name {
            pub const ARITY: usize = count_idents!($($op)+);

            pub fn new($($cap: $cty,)* loads: &[u16], stores: &[Option<u16>]) -> Self {
                assert_eq!(loads.len(), Self::ARITY);
                assert_eq!(stores.len(), Self::ARITY);
                const { assert!(count_idents!($($cap)*) <= MAX_HOLES) };
                Self { $($cap,)* loads: loads.into(), stores: stores.into() }
            }

            /// The body, shared by the interpreter and the stencil.
            #[inline(always)]
            unsafe fn __run<'a, 'b, 'src, 'intern>(
                $($cap: $cty,)*
                $owner: &'a mut Owner,
                $state: &'b mut RunState<'src, 'intern>,
                $base: *mut LBoxed<'src, 'intern>,
                __ops: *mut LBoxed<'src, 'intern>,
            ) {
                let mut __i = 0usize;
                $(
                    let $op: &mut LBoxed<'src, 'intern> = unsafe { &mut *__ops.add(__i) };
                    __i += 1;
                )+
                unsafe { $body }
            }

            /// The stencil with this op's operands at window offset `K`.
            pub extern "rust-preserve-none" fn __stencil<'a, 'b, 'src, 'intern, const K: usize>(
                owner: &'a mut Owner,
                state: &'b mut RunState<'src, 'intern>,
                base: *mut LBoxed<'src, 'intern>,
                w0: LBoxed<'src, 'intern>,
                w1: LBoxed<'src, 'intern>,
                w2: LBoxed<'src, 'intern>,
                w3: LBoxed<'src, 'intern>,
            ) {
                if K + Self::ARITY > WINDOW {
                    // Never instantiated for use: `stencil(k)` rejects such `k`.
                    unsafe { core::hint::unreachable_unchecked() }
                }
                let mut __w = [w0, w1, w2, w3];
                let mut __h = 0usize;
                $(
                    let $cap: $cty = unsafe { <$cty as Capture>::from_bits(hole(__h)) };
                    __h += 1;
                )*
                unsafe { Self::__run($($cap,)* &mut *owner, &mut *state, base, __w.as_mut_ptr().add(K)) };
                become __next(owner, state, base, __w[0], __w[1], __w[2], __w[3])
            }
        }

        impl Window for $name {
            fn name(&self) -> &'static str { stringify!($name) }
            fn arity(&self) -> usize { Self::ARITY }
            fn loads(&self) -> &[u16] { &self.loads }
            fn stores(&self) -> &[Option<u16>] { &self.stores }
            fn captures(&self) -> Captures {
                smallvec![$(Capture::to_bits(self.$cap)),*]
            }
            fn stencil(&self, k: usize) -> usize {
                assert!(k + Self::ARITY <= WINDOW, "{} at offset {k} overruns the window", stringify!($name));
                match k {
                    0 => Self::__stencil::<0> as *const () as usize,
                    1 => Self::__stencil::<1> as *const () as usize,
                    2 => Self::__stencil::<2> as *const () as usize,
                    3 => Self::__stencil::<3> as *const () as usize,
                    _ => unreachable!(),
                }
            }
            unsafe fn run<'src, 'intern>(
                &self,
                owner: &mut Owner,
                state: &mut RunState<'src, 'intern>,
                base: *mut LBoxed<'src, 'intern>,
                ops: *mut LBoxed<'src, 'intern>,
            ) {
                unsafe { Self::__run($(self.$cap,)* owner, state, base, ops) }
            }
        }
    };
}

// ---- ops ------------------------------------------------------------------

/// A guarded number's value (the specializer only emits these after a Number
/// guard, so this never fails; unchecked to keep the stencil panic-free).
#[inline(always)]
fn num(v: LBoxed<'_, '_>) -> f64 {
    unsafe { v.as_number().unwrap_unchecked() }
}

/// Declare the three numeric window ops for one operator: both operands in the
/// window, rhs constant (capture), lhs constant (capture).
macro_rules! numeric_windows {
    ($vv:ident, $vk:ident, $kv:ident, $op:tt) => {
        windowed! {
            /// `dest = lhs OP rhs`, both guarded numbers in the window.
            pub $vv [] (owner, state, base) (a, b) {
                *a = LBoxed::from_number(num(*a) $op num(*b));
            }
        }
        windowed! {
            /// `dest = lhs OP k`, lhs a guarded number in the window, `k` a constant.
            pub $vk [k: f64] (owner, state, base) (a) {
                *a = LBoxed::from_number(num(*a) $op k);
            }
        }
        windowed! {
            /// `dest = k OP rhs`, rhs a guarded number in the window, `k` a constant.
            pub $kv [k: f64] (owner, state, base) (a) {
                *a = LBoxed::from_number(k $op num(*a));
            }
        }
    };
}

numeric_windows!(NumAdd, NumAddK, NumKAdd, +);
numeric_windows!(NumSub, NumSubK, NumKSub, -);
numeric_windows!(NumMul, NumMulK, NumKMul, *);
numeric_windows!(NumDiv, NumDivK, NumKDiv, /);

windowed! {
    /// Flush the whole window to `base[0..WINDOW]`. Used to observe a copy&patch
    /// chain's result; the JIT's flush-to-stack-home primitive.
    pub Flush [] (owner, state, base) (a, b, c, d) {
        *base.add(0) = *a;
        *base.add(1) = *b;
        *base.add(2) = *c;
        *base.add(3) = *d;
    }
}

/// The window op for `dest = lhs OP rhs` with both operands guarded numbers, or
/// `None` if `OP` has no copy&patch-safe body yet (MOD/POW call into libm).
pub fn numeric(op: Opcode, dest: usize, lhs: usize, rhs: usize) -> Option<std::rc::Rc<dyn Window>> {
    let (l, s) = ([lhs as u16, rhs as u16], [Some(dest as u16), None]);
    Some(match op {
        Opcode::ADD => std::rc::Rc::new(NumAdd::new(&l, &s)),
        Opcode::SUB => std::rc::Rc::new(NumSub::new(&l, &s)),
        Opcode::MUL => std::rc::Rc::new(NumMul::new(&l, &s)),
        Opcode::DIV => std::rc::Rc::new(NumDiv::new(&l, &s)),
        _ => return None,
    })
}

/// The window op for a numeric op with one constant operand `k`: `dest = slot OP
/// k` if `k_is_rhs`, else `dest = k OP slot`. `None` for MOD/POW.
pub fn numeric_const(
    op: Opcode,
    dest: usize,
    slot: usize,
    k: f64,
    k_is_rhs: bool,
) -> Option<std::rc::Rc<dyn Window>> {
    let (l, s) = ([slot as u16], [Some(dest as u16)]);
    Some(match (op, k_is_rhs) {
        (Opcode::ADD, true) => std::rc::Rc::new(NumAddK::new(k, &l, &s)),
        (Opcode::SUB, true) => std::rc::Rc::new(NumSubK::new(k, &l, &s)),
        (Opcode::MUL, true) => std::rc::Rc::new(NumMulK::new(k, &l, &s)),
        (Opcode::DIV, true) => std::rc::Rc::new(NumDivK::new(k, &l, &s)),
        (Opcode::ADD, false) => std::rc::Rc::new(NumKAdd::new(k, &l, &s)),
        (Opcode::SUB, false) => std::rc::Rc::new(NumKSub::new(k, &l, &s)),
        (Opcode::MUL, false) => std::rc::Rc::new(NumKMul::new(k, &l, &s)),
        (Opcode::DIV, false) => std::rc::Rc::new(NumKDiv::new(k, &l, &s)),
        _ => return None,
    })
}

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

/// Copy the stencil at `addr`. Asserts its last instruction is the `become
/// __next` jmp (slicing it for fall-through is only valid then) and finds its
/// hole loads by matching each disp32's RIP target against a hole's GOT slot.
pub unsafe fn stencil_body(relocs: &Relocs, addr: usize) -> Body {
    let size = *relocs.sizes.get(&(addr as u64)).expect("stencil in symtab") as usize;
    let code = unsafe { core::slice::from_raw_parts(addr as *const u8, size) };
    assert!(size >= 5 && code[size - 5] == 0xe9, "stencil {addr:#x} does not end in a jmp");
    let rel = i32::from_le_bytes(code[size - 4..].try_into().unwrap());
    assert_eq!(
        addr.wrapping_add(size).wrapping_add(rel as isize as usize),
        next_addr(),
        "stencil {addr:#x} does not end in `become __next`"
    );
    let code = code[..size - 5].to_vec();

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

/// Copy&patch `ops` — `(stencil address, captures)` — into one executable
/// buffer: bodies concatenated (so the register window falls through), then
/// `tail`, then the shared hole-value pool every hole load is repointed at.
pub unsafe fn assemble(relocs: &Relocs, ops: &[(usize, Captures)], tail: &[u8]) -> ExecutableBuffer {
    let mut code = Vec::new();
    let mut patches: Vec<(usize, u64)> = Vec::new();
    for (addr, captures) in ops {
        let body = unsafe { stencil_body(relocs, *addr) };
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

#[cfg(test)]
mod tests {
    use super::*;
    use dynasmrt::AssemblyOffset;

    /// Copy&patch the real numeric stencils into a chain over the register window
    /// and run it: prepare (a, b, c), Add at offset 1 (b+c), Mul at offset 0
    /// (a*prev), AddK at offset 0 (a capture/hole), then Flush.
    #[test]
    #[cfg_attr(debug_assertions, ignore = "stencils must be built optimized: run `just test-stencils`")]
    fn copy_and_patch_numeric_chain() {
        let relocs = Relocs::load();
        let add = NumAdd { loads: smallvec![0, 0], stores: smallvec![None, None] };
        let mul = NumMul { loads: smallvec![0, 0], stores: smallvec![None, None] };
        let addk = NumAddK { k: 0.5, loads: smallvec![0], stores: smallvec![None] };
        let flush = Flush { loads: smallvec![0; 4], stores: smallvec![None; 4] };
        let ops = [
            (add.stencil(1), add.captures()),
            (mul.stencil(0), mul.captures()),
            (addk.stencil(0), addk.captures()),
            (flush.stencil(0), flush.captures()),
        ];
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
