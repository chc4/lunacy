#![feature(trait_alias, specialization, iter_intersperse, slice_ptr_get)]
// For LBBV
#![feature(coroutines, coroutine_trait, coroutine_clone, stmt_expr_attributes)]
// For JIT
#![feature(ptr_metadata, rust_preserve_none_cc, rust_cold_cc, iter_map_windows)]
// For copy&patch window stencils
#![feature(linkage, explicit_tail_calls)]
#![feature(fn_traits, unboxed_closures, adt_const_params)]
// For GC
#![feature(core_intrinsics, generic_const_exprs)]

pub mod chunk;
pub mod stack;
pub mod lboxed;
pub mod vm;
pub mod perf;
// The generator (lazy basic-block versioner / specializer) compiles with the
// `lbbv` feature; the native code generator adds `jit` on top. Interpreter-only
// builds (`--no-default-features --features magic`) enable neither and stay
// entirely in `vm::run`.
#[cfg(feature = "lbbv")]
pub mod generator;
#[cfg(feature = "lbbv")]
pub mod window;
#[cfg(feature = "jit")]
pub mod window_alloc;
#[cfg(feature = "jit")]
pub mod trace;
#[cfg(feature = "jit")]
pub mod jit;
#[cfg(feature = "jit_disasm")]
pub mod disasm;
pub mod gc;
pub mod library;

pub use vm::Vm;
/// Marker branding the per-thread cell owner. `Owner` is unique per thread — a second
/// `Owner::new` panics — which is what pins one VM per thread; see Note [Scoped heap] in `gc`.
pub struct TlcOwner;
/// The cell owner handle, threaded through every read or write of a GC-managed [`TLCell`].
pub type Owner = qcell::TLCellOwner<TlcOwner>;

const _: () = assert!(core::mem::size_of::<Owner>() == 0, "Owner is a zero-sized token");

/// An `Owner` token for code the thread's one real owner is lent to but not
/// passed: the JIT's calling convention and its stencils leave the
/// zero-sized token out, and forge it where a callee wants one.
///
/// # Safety
/// The thread's real `Owner` must be lent to the caller for as long as the
/// forged one is used, as it is to JIT code for the duration of the call
/// into it.
#[inline(always)]
pub unsafe fn forge_owner<'a>() -> &'a mut Owner {
    unsafe { core::ptr::NonNull::dangling().as_mut() }
}
pub use qcell::TLCell;

pub use log::debug;
pub use log::info;
pub use log::warn;
