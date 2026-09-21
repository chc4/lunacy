#![feature(trait_alias, specialization, iter_intersperse, slice_ptr_get)]
// For LBBV
#![feature(coroutines, coroutine_trait, coroutine_clone, stmt_expr_attributes)]
// For JIT
#![feature(ptr_metadata, rust_preserve_none_cc, iter_map_windows)]
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
#[cfg(feature = "jit")]
pub mod jit;
pub mod gc;

pub use vm::Vm;
/// Marker branding the per-thread cell owner. `Owner` is unique per thread — a second
/// `Owner::new` panics — which is what pins one VM per thread; see Note [Scoped heap] in `gc`.
pub struct TlcOwner;
/// The cell owner handle, threaded through every read or write of a GC-managed [`TLCell`].
pub type Owner = qcell::TLCellOwner<TlcOwner>;
pub use qcell::TLCell;

pub use log::debug;
pub use log::info;
pub use log::warn;
