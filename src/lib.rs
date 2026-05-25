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
pub mod vm;
pub mod perf;
pub mod generator;
pub mod jit;
pub mod gc;

pub use vm::Vm;
pub use qcell::{TCell, TCellOwner};

pub use log::debug;
pub use log::info;
pub use log::warn;
