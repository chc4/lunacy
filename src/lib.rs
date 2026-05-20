#![feature(trait_alias, specialization, iter_intersperse, atomic_try_update, slice_ptr_get)]
// For LBBV
#![feature(coroutines, coroutine_trait, coroutine_clone, stmt_expr_attributes)]
// For JIT
#![feature(ptr_metadata, rust_preserve_none_cc, iter_map_windows)]
#![feature(fn_traits, unboxed_closures, adt_const_params)]

pub mod chunk;
pub mod stack;
pub mod vm;
pub mod perf;
pub mod generator;
pub mod jit;

pub use vm::Vm;
pub use qcell::TCellOwner;
