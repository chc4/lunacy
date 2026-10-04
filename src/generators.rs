#![allow(unused_variables, unused_assignments, unused)]

use std::borrow::Cow;
use std::collections::HashMap;
use std::ops::{Coroutine, CoroutineState, Deref};
use std::pin::Pin;
use std::rc::Rc;
use std::cell::{Cell, RefCell};

use crate::vm::{CallstackEntry, HashWitness, NClosure, NativeFunc, Opcode, Location, Upvalue};
use qcell::{LCell, LCellOwner};
use crate::Owner;
use crate::vm::{Tc, Vm, Widen};
use crate::vm::{BlockId, HashRef};
use crate::vm::{LClosure, LProto};
use crate::vm::{LValue, LType, Number, Table, FVec, LBoxed, LCanon, IStr};
use crate::lboxed::is_integer;
use crate::vm::{InstructionDecode, Unpacker};
use crate::vm::RunState;
use crate::vm::LConstant;
use crate::vm::InternedHasher;
use crate::chunk::Constant;
use crate::chunk::Instruction;
use crate::window::{windowed, Access, Window};
// The native code generator (`JitContext`) and its per-block `JitInfo` (dynasm
// buffer + hotness tiering) are only needed with the `jit` feature.
#[cfg(feature = "jit")]
use crate::jit::{JitInfo, JitContext};
use crate::gc::{Mark, Heap, GcCtx};

use crate::{debug, info, warn};
use smallvec::SmallVec;

use crate::specialize::*;
#[cfg(feature = "unreachable")]
use crate::unreachable;

macro_rules! define_exec {
    ($name:ident, [$($cap:ident: $cap_ty:ty),*], [$($const_param:ident: $const_ty:ty),*],
        |$owner:ident, $state:ident, $($args:ident),*| $body:block) =>
    {
        #[derive(Clone)]
        pub struct $name<$(const $const_param: $const_ty),*> {
            $(pub $cap: $cap_ty),*
        }

        impl<$(const $const_param: $const_ty),*> FnOnce<(&mut Owner, &mut RunState<'_, '_>)> for $name<$($const_param),*> {
            type Output = ();
            #[inline(always)]
            extern "rust-call" fn call_once(self, args: (&mut Owner, &mut RunState<'_, '_>)) {
                self.call(args)
            }
        }

        impl<$(const $const_param: $const_ty),*> FnMut<(&mut Owner, &mut RunState<'_, '_>)> for $name<$($const_param),*> {
            #[inline(always)]
            extern "rust-call" fn call_mut(&mut self, args: (&mut Owner, &mut RunState<'_, '_>)) {
                self.call(args)
            }
        }

        impl<$(const $const_param: $const_ty),*> Fn<(&mut Owner, &mut RunState<'_, '_>)> for $name<$($const_param),*> {
            #[inline(always)]
            extern "rust-call" fn call(&self, (owner, state): (&mut Owner, &mut RunState<'_, '_>)) {
                let $name { $($cap),* } = self;
                $(let $args = *$cap;)*
                let $owner = owner;
                let $state = state;
                $body
            }
        }
    };
}

/// An arithmetic operation's instance of a `Window`, specialized for the specific constant `OP:
/// Opcode`.
macro_rules! dispatch_numeric_window {
    ($opcode:expr, $name:ident, [$($p:expr),*], ($($arg:expr),*)) => {
        match $opcode {
            Opcode::ADD => Rc::new($name::<{Opcode::ADD} $(, {$p})*>::new($($arg),*)) as Rc<dyn Window>,
            Opcode::SUB => Rc::new($name::<{Opcode::SUB} $(, {$p})*>::new($($arg),*)),
            Opcode::MUL => Rc::new($name::<{Opcode::MUL} $(, {$p})*>::new($($arg),*)),
            Opcode::DIV => Rc::new($name::<{Opcode::DIV} $(, {$p})*>::new($($arg),*)),
            Opcode::MOD => Rc::new($name::<{Opcode::MOD} $(, {$p})*>::new($($arg),*)),
            Opcode::POW => Rc::new($name::<{Opcode::POW} $(, {$p})*>::new($($arg),*)),
            _ => unreachable!(),
        }
    };
}

/// `dispatch_numeric_window`, for the integer ops. See Note [Integers].
macro_rules! dispatch_integer_window {
    ($opcode:expr, $name:ident, ($($arg:expr),*)) => {
        match $opcode {
            Opcode::ADD => Rc::new($name::<{Opcode::ADD}>::new($($arg),*)) as Rc<dyn Window>,
            Opcode::SUB => Rc::new($name::<{Opcode::SUB}>::new($($arg),*)),
            Opcode::MUL => Rc::new($name::<{Opcode::MUL}>::new($($arg),*)),
            Opcode::MOD => Rc::new($name::<{Opcode::MOD}>::new($($arg),*)),
            _ => unreachable!(),
        }
    };
}

macro_rules! dispatch_compare_window {
    ($opcode:expr, $name:ident, [$($p:expr),*], ($($arg:expr),*)) => {
        match $opcode {
            Opcode::EQ => Rc::new($name::<{Opcode::EQ} $(, {$p})*>::new($($arg),*)) as Rc<dyn Window>,
            Opcode::LT => Rc::new($name::<{Opcode::LT} $(, {$p})*>::new($($arg),*)),
            Opcode::LE => Rc::new($name::<{Opcode::LE} $(, {$p})*>::new($($arg),*)),
            _ => unreachable!(),
        }
    };
}

/// Whether an operand is in the integer encoding. A constant operand is always
/// treated as a double. See Note [Integers].
macro_rules! integer_encoded {
    ($rk:expr) => {{
        if ($rk & 0x100) != 0 {
            false
        } else {
            (yield YieldOp::GuardCType($rk, CType::Type(LType::Integer))) == ResumeArg::Matched
        }
    }};
}

/// Whether a numeric op computes on integers: both its operands are, an
/// integral constant counting as one. See Note
/// [Integers].
///
/// Only an operand already known to be an integer (a register typed so, or an
/// integral constant) makes the other register's integer-ness worth asking:
/// asking can transition that slot's static type, modifying the specialization
/// context and duplicating versions. Not asking when the other operand is an
/// integral constant would compute an integer register plus a constant as a
/// double, changing its encoding, so a counter the context can't type (an
/// upvalue, a field) would alternate between encodings.
///
/// The other register is asked about even when its type is already known, so
/// the path through this macro always results in a stable `SubPc` that allows
/// for reuse. See Note [Subblocks].
macro_rules! integer_operands {
    ($lhs:expr, $rhs:expr) => {{
        let integer = ResumeArg::Type(CType::Type(LType::Integer));
        let lt = (yield YieldOp::TypeofRk($lhs)) == integer;
        let rt = (yield YieldOp::TypeofRk($rhs)) == integer;
        if lt && ($rhs & 0x100) == 0 {
            integer_encoded!($rhs)
        } else if rt && ($lhs & 0x100) == 0 {
            integer_encoded!($lhs)
        } else {
            lt && rt
        }
    }};
}

pub fn emit_loadk(bx: u32, c: LType, dest: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        // The constant's boxed value is the op's hole. It is already in canonical
        // form (an integer if possible). See Note [Integers].
        windowed!(LoadK, [bits: u64], [], |owner, state, base| (out dest) {
            // A constant's value lives as long as its prototype.
            *dest = LBoxed::from_bits(bits);
        });
        match c {
            LType::Integer | LType::Double => {
                let ResumeArg::Type(t) = (yield YieldOp::TypeofK(bx as usize)) else { unreachable!() };
                let ResumeArg::Boxed(bits) = (yield YieldOp::BoxedK(bx as usize)) else { unreachable!() };
                yield YieldOp::ExecWindow(Rc::new(LoadK::new(bits, &[dest])));
                yield YieldOp::SetCTypes(vec![(dest, t)]);
            },
            LType::String => {
                let ResumeArg::Boxed(bits) = (yield YieldOp::BoxedK(bx as usize)) else { unreachable!() };
                yield YieldOp::ExecWindow(Rc::new(LoadK::new(bits, &[dest])));
                yield YieldOp::SetTypes(vec![(dest, LType::String)]);
            },
            _ => unreachable!(),
        }
        return arg;
    }
}

/// `R(A) := (Bool)B; if (C) pc++`, `pc` being the next instruction's.
pub fn emit_loadbool(dest: usize, value: bool, skip: bool, pc: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        windowed!(LoadBool, [value: u8], [], |owner, state, base| (out dest) {
            *dest = LBoxed::from_bool(value != 0);
        });
        yield YieldOp::ExecWindow(Rc::new(LoadBool::new(value as u8, &[dest])));
        yield YieldOp::SetTypes(vec![(dest, LType::Bool)]);
        if skip {
            arg = yield YieldOp::GetBlock(pc + 1);
            let ResumeArg::BlockId(target) = arg else { unreachable!() };
            arg = yield YieldOp::Jump(target);
        }
        arg
    }
}

/// `R(A) := ... := R(B) := nil`.
pub fn emit_loadnil(a: usize, b: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        windowed!(LoadNil, [], [], |owner, state, base| (out dest) {
            *dest = LBoxed::NIL;
        });
        for dest in a..=b {
            yield YieldOp::ExecWindow(Rc::new(LoadNil::new(&[dest])));
        }
        yield YieldOp::SetTypes((a..=b).map(|dest| (dest, LType::Nil)).collect());
        arg
    }
}

// Load a field through its hash key's witness. See Note [Hash witnesses].
windowed!(GetTableHref, [href: u8], [], |owner, state, base| (out dest) {
    // Written by the frame's `href_init` already. See Note [Hash
    // witnesses].
    let witness = state.hash_witnesses[state.witness_base + href as usize];
    debug!("gettable_href with {:?}", &witness);
    // The witness holds for the table (its epoch, or no hazard
    // since), so its value's address does. See Note [Hash witnesses].
    let val1 = *witness.value.cast::<LBoxed<'_, '_>>();

    debug!("gettable_href fetched {val1:?}");
    *dest = val1;
});

// GETGLOBAL and SETGLOBAL through a global's cache, at `cache`. See Note
// [Global caches].
// A cache that misses is refilled out of line.
windowed!(GetGlobal, [cache: usize], [], |owner, state, base| (out dest) {
    let cache = &*(cache as *const GlobalCache);
    match cache.hit() {
        Some(entry) => {
            #[cfg(debug_assertions)]
            {
                let key: &LCanon<'_, '_> = core::mem::transmute(&cache.key);
                assert_eq!(state._G.ro(owner).hash.get(key).map(|value| value as *const _ as usize), Some(entry as usize), "a stale global cache");
            }
            *dest = *entry.cast();
            false
        },
        None => true,
    }
} rejoin {
    let cache = &*(cache as *const GlobalCache);
    *dest = cache.refill(owner, &state._G).map_or(LBoxed::NIL, |entry| *entry.cast());
});
// A store that hits the cache and keeps the field's type stores in place; any
// other, or one needing the write barrier, goes out of line.
windowed!(SetGlobal, [cache: usize], [], |owner, state, base| (value) {
    let cache = &*(cache as *const GlobalCache);
    match cache.hit() {
        // Hash keys of registers holding the environment know a field's type
        // by its epoch. See Note [Field types].
        Some(entry) if !state._G.barrier_pending() && (*entry.cast::<LBoxed<'_, '_>>()).unbox().typeof_() == value.unbox().typeof_() => {
            *entry.cast::<LBoxed<'_, '_>>() = value;
            false
        },
        _ => true,
    }
} rejoin {
    let cache = &*(cache as *const GlobalCache);
    match cache.hit().or_else(|| cache.refill(owner, &state._G)) {
        Some(entry) => {
            let entry = &mut *entry.cast::<LBoxed<'_, '_>>();
            // See Note [Field types].
            if entry.unbox().typeof_() != value.unbox().typeof_() {
                state._G.rw(owner).epoch += 1;
            }
            *entry = value;
            // Last. See Note [Write barriers].
            state._G.barrier_back();
        },
        None => set_global(owner, state, cache, value),
    }
});

/// A store to a global the environment lacks.
fn set_global<'src, 'intern>(owner: &mut Owner, state: &mut RunState<'src, 'intern>, cache: &GlobalCache, value: LBoxed<'src, 'intern>) {
    let key: LCanon<'src, 'intern> = unsafe { core::mem::transmute(cache.key) };
    let mut env = state._G.clone();
    env.set(owner, key.boxed(), value, state.intern);
}

/// GETGLOBAL: `R(A) := Gbl[Kst(Bx)]`, with `k` = Bx. See Note [Global caches].
pub fn emit_getglobal(dest: usize, k: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static {
    #[coroutine]
    move |mut arg: ResumeArg| {
        let ResumeArg::Cache(cache) = (yield YieldOp::GlobalCache(k)) else { unreachable!() };
        arg = yield YieldOp::ExecWindow(Rc::new(GetGlobal::new(cache as usize, &[dest])));
        yield YieldOp::SetTypes(vec![(dest, LType::Unknown)]);
        arg
    }
}

/// SETGLOBAL: `Gbl[Kst(Bx)] := R(A)`, with `k` = Bx. See Note [Global caches].
pub fn emit_setglobal(src: usize, k: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin + 'static {
    #[coroutine]
    move |mut arg: ResumeArg| {
        let ResumeArg::Cache(cache) = (yield YieldOp::GlobalCache(k)) else { unreachable!() };
        arg = yield YieldOp::ExecWindow(Rc::new(SetGlobal::new(cache as usize, &[src])));
        // A register may hold the environment: its hash keys of this global must
        // check the epoch again.
        yield YieldOp::SetKeyHazards(k);
        arg
    }
}

// `GuardDynamic` tests: whether a `CType::Type(LType::Integer)` key, in a register or the
// constant `k`, is in a table's array part. See Note [Dynamic guards].
crate::window::windowed!(guard InArray, [], [], |owner, state, base| (table, key) {
    let LValue::Table(tab) = table.unbox() else { unreachable!() };
    integer_slot(key.as_int()) < tab.ro(owner).array.len()
});
crate::window::windowed!(guard InArrayK, [k: i32], [], |owner, state, base| (table) {
    let LValue::Table(tab) = table.unbox() else { unreachable!() };
    integer_slot(k) < tab.ro(owner).array.len()
});


pub fn emit_gettable(a: usize, b: usize, c: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Guard(b, LType::Table);
        if arg != ResumeArg::Matched {
            let have = yield YieldOp::Typeof(b);
            arg = yield YieldOp::Exec(ResidualExec::new("gettable_meta", Rc::new(move |owner, state| {
                panic!("gettable_meta {:?} {:?} {:?}", &state.vals, &state.vals[state.base + b], have)
            })));
            yield YieldOp::SetTypes(vec![(a, LType::Unknown)]);
            return arg;
        }
        // Object shape specialization
        arg = yield YieldOp::HashKey(b, c);
        if let ResumeArg::HashRef(hc, htype) = arg {
            arg = yield YieldOp::ExecWindow(Rc::new(GetTableHref::new(hc.0, &[a])));
            // Its type: the hash key's, or found out. See Note [Field types].
            yield YieldOp::FieldType(a, hc);
        } else {
            // An integer key in the array part, potentially from a constant `k`. See Note [Dynamic guards].
            let integer = match yield YieldOp::GuardCType(c, CType::Type(LType::Integer)) {
                ResumeArg::MatchedConst(k) => {
                    let ResumeArg::Integer(k) = (yield YieldOp::IntegerK(k)) else { unreachable!() };
                    Some(Some(k))
                },
                ResumeArg::Matched => Some(None),
                _ => None,
            };
            let in_array = match integer {
                Some(Some(k)) => yield YieldOp::GuardDynamic(Rc::new(InArrayK::new(k, &[b]))),
                Some(None) => yield YieldOp::GuardDynamic(Rc::new(InArray::new(&[b, c]))),
                None => yield YieldOp::Decided(false),
            };
            if let (Some(Some(k)), ResumeArg::Matched) = (integer, &in_array) {
                windowed!(GetTableArray, [k: i32], [], |owner, state, base| (table, out dest) {
                    let LValue::Table(tab) = table.unbox() else { unreachable!() };
                    *dest = tab.ro(owner).array[integer_slot(k)];
                });
                arg = yield YieldOp::ExecWindow(Rc::new(GetTableArray::new(k, &[b, a])));
                yield YieldOp::ArrayType(a, b);
            } else if let (Some(None), ResumeArg::Matched) = (integer, &in_array) {
                windowed!(GetTableInteger, [], [], |owner, state, base| (table, key, out dest) {
                    let LValue::Table(tab) = table.unbox() else { unreachable!() };
                    *dest = tab.ro(owner).array[integer_slot(key.as_int())];
                });
                arg = yield YieldOp::ExecWindow(Rc::new(GetTableInteger::new(&[b, c, a])));
                yield YieldOp::ArrayType(a, b);
            } else {
                // Any other key: through `gettable`.
                arg = yield YieldOp::Exec(ResidualExec::new("gettable", Rc::new(move |owner, state| {
                    let kc = match Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, c as u16) {
                        Ok(c) => Cow::Owned(LValue::from(c)),
                        Err(lv) => Cow::Owned(lv.unbox()),
                    };
                    debug!("gettable {:?}", &kc);
                    let val_b = state.vals[state.base + b as usize].unbox();
                    state.vals[state.base + a as usize] = LBoxed::box_lvalue(val_b.gettable(owner, kc, state.intern));
                })));
                yield YieldOp::SetTypes(vec![(a, LType::Unknown)]);
            }
        }
        arg
    }
}

/// What a store through a hash key's witness does to its field's type, which
/// the context knows as the hash key's type (`known_type`). See Note [Hash
/// witnesses].
#[derive(Debug, Clone, Copy, PartialEq, Eq, core::marker::ConstParamTy)]
pub enum Retype {
    /// The value has the field's known type.
    Same,
    /// The value has another known type, which becomes the field's: the table
    /// moves to a new epoch, and the witness with it.
    Known,
    /// The value's type is unknown, and the field keeps its known type
    /// (`UpdateHashRef`): the table moves to a new epoch but the witness
    /// doesn't, so the next access checks the field's type (`HashGuard`).
    Unknown,
}

/// Widen `tab`'s kind for a store of `value`, as `W` says.
#[inline(always)]
fn store_kind<'src, 'intern, const W: Widen>(owner: &mut Owner, tab: &Tc<Table<'src, 'intern>>, value: LBoxed<'src, 'intern>) {
    tab.rw(owner).widen_by(W, value);
}

/// Store `value` into `tab`'s array part at `slot`, widening its kind as `W`
/// says. A value that `MAY_BE_NIL` and is nil drops the nils ending the array,
/// and past its end stores nothing (so the store repeats safely, as
/// `check_windows` repeats it). See Note [Array length] in `vm`.
#[inline(always)]
fn store_array<'src, 'intern, const W: Widen, const MAY_BE_NIL: bool>(owner: &mut Owner, tab: &Tc<Table<'src, 'intern>>, slot: usize, value: LBoxed<'src, 'intern>) {
    if MAY_BE_NIL && value.bits() == LBoxed::NIL.bits() {
        if slot < tab.ro(owner).array.len() {
            tab.rw(owner).array[slot] = value;
            store_kind::<W>(owner, tab, value);
            tab.rw(owner).trim();
        }
        return;
    }
    tab.rw(owner).array[slot] = value;
    store_kind::<W>(owner, tab, value);
}

/// `$make!` of the const `Widen` that `$how` is.
macro_rules! with_widen {
    ($how:expr, $make:ident) => {
        match $how {
            Widen::No => $make!({ Widen::No }),
            Widen::Decode => $make!({ Widen::Decode }),
            Widen::Bit(LType::Nil) => $make!({ Widen::Bit(LType::Nil) }),
            Widen::Bit(LType::Bool) => $make!({ Widen::Bit(LType::Bool) }),
            Widen::Bit(LType::String) => $make!({ Widen::Bit(LType::String) }),
            Widen::Bit(LType::Closure) => $make!({ Widen::Bit(LType::Closure) }),
            Widen::Bit(LType::Table) => $make!({ Widen::Bit(LType::Table) }),
            Widen::Bit(LType::Integer) => $make!({ Widen::Bit(LType::Integer) }),
            Widen::Bit(LType::Double) => $make!({ Widen::Bit(LType::Double) }),
            Widen::Bit(LType::Unknown) => unreachable!("a store of a known value of unknown representation"),
        }
    };
}

/// How storing a value of type `new_type` changes a field known as `htype`. A
/// field whose type isn't known yet is never `Same`: its value may have any
/// type. See Note [Field types].
fn retype(new_type: LType, htype: LType) -> Retype {
    if new_type == htype && htype != LType::Unknown {
        Retype::Same
    } else if new_type == LType::Unknown {
        Retype::Unknown
    } else {
        Retype::Known
    }
}

/// Store through `href`'s witness into `tab`, bumping the table's epoch if the
/// field's type changes (see `Retype`), and leaving its write barrier to the
/// caller, after it.
fn store_field<'src, 'intern>(owner: &mut Owner, state: &mut RunState<'src, 'intern>, tab: &Tc<Table<'src, 'intern>>, value: LBoxed<'src, 'intern>, href: u8, expected: LType, retype: Retype) {
    let hidx = state.witness_base + href as usize;
    let witness = state.hash_witnesses[hidx];
    debug!("settable_href with {:?} {:?}", &witness, expected);
    // See Note [Hash witnesses].
    let val1 = unsafe { &mut *witness.value.cast::<LBoxed<'src, 'intern>>() };
    debug!("settable_href {:?} {:?}", &val1, expected);
    #[cfg(debug_assertions)]
    assert!(expected.accepts(val1.unbox().typeof_()));
    *val1 = value;
    match retype {
        Retype::Same => {}
        Retype::Known => {
            tab.rw(owner).epoch += 1;
            state.hash_witnesses[hidx].epoch = tab.rw(owner).epoch;
        }
        Retype::Unknown => tab.rw(owner).epoch += 1,
    }
}

// Store through a hash key's witness into a register's table.
windowed!(SetTableHref, [href: u8, expected: LType], [RETYPE: Retype], |owner, state, base| (table, value) {
    let LValue::Table(tab) = table.unbox() else { unreachable!() };
    store_field(owner, state, &tab, value, href, expected, RETYPE);
    // Last. See Note [Write barriers].
    tab.barrier_pending()
} rejoin {
    let LValue::Table(tab) = table.unbox() else { unreachable!() };
    tab.barrier_slow();
});
windowed!(SetTableHrefK, [href: u8, expected: LType, value: u64], [RETYPE: Retype], |owner, state, base| (table) {
    let LValue::Table(tab) = table.unbox() else { unreachable!() };
    // A constant's value lives as long as its prototype.
    let value = LBoxed::from_bits(value);
    store_field(owner, state, &tab, value, href, expected, RETYPE);
    // Last. See Note [Write barriers].
    tab.barrier_pending()
} rejoin {
    let LValue::Table(tab) = table.unbox() else { unreachable!() };
    tab.barrier_slow();
});

pub fn emit_settable(a: usize, b: usize, c: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Guard(a, LType::Table);
        if arg != ResumeArg::Matched {
            arg = yield YieldOp::Exec(ResidualExec::new("settable_meta", Rc::new(move |owner, state| {
                let key: LValue = match Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, b as u16) {
                    Ok(b) => LValue::from(b),
                    Err(lv) => lv.unbox(),
                };
                // The debugging key `closure.__jit = ...` (feature `magic`): the
                // closure's entry blocks compile when next entered. See
                // `Specializer::force_jit`.
                match (state.vals[state.base + a].unbox(), key) {
                    #[cfg(feature = "magic")]
                    (LValue::LClosure(lc), LValue::InternedString(key)) if key.as_bytes() == b"__jit" => {
                        state.force_jit.push(lc.ro(owner).prototype);
                    },
                    _ => panic!("settable_meta {:?}", &state.vals),
                }
            })));
            arg = yield YieldOp::SetHazards(None, None);
            return arg;
        }
        // An integer key in the array part. Potentially from a constant (`k`).
        // See Note [Dynamic guards].
        let integer = match yield YieldOp::GuardCType(b, CType::Type(LType::Integer)) {
            ResumeArg::MatchedConst(k) => {
                let ResumeArg::Integer(k) = (yield YieldOp::IntegerK(k)) else { unreachable!() };
                Some(Some(k))
            },
            ResumeArg::Matched => Some(None),
            _ => None,
        };
        let in_array = match integer {
            Some(Some(k)) => yield YieldOp::GuardDynamic(Rc::new(InArrayK::new(k, &[a]))),
            Some(None) => yield YieldOp::GuardDynamic(Rc::new(InArray::new(&[a, b]))),
            None => yield YieldOp::Decided(false),
        };
        // A constant value's boxed value is the op's hole.
        let constant = if c & 0x100 != 0 && matches!(in_array, ResumeArg::Matched) {
            let ResumeArg::Boxed(bits) = (yield YieldOp::BoxedK(c & 0xff)) else { unreachable!() };
            Some(bits)
        } else {
            None
        };
        // Counts the store about to be emitted in `PerfCounters::$counters` by
        // what's known of the value's type.
        #[cfg(feature = "store_types")]
        macro_rules! count_store {
            ($counters:ident) => {
                let ResumeArg::Type(t) = (yield YieldOp::TypeofRk(c)) else { unreachable!() };
                let known = match t { CType::Type(LType::Unknown) => 0, CType::Number => 1, _ => 2 };
                yield YieldOp::Exec(ResidualExec::new("count_store", Rc::new(move |owner, state| {
                    state.counters.$counters[known].increment();
                })));
            };
        }
        #[cfg(not(feature = "store_types"))]
        macro_rules! count_store {
            ($counters:ident) => {};
        }
        if let (Some(_), ResumeArg::Matched) = (integer, &in_array) {
            count_store!(array_stores);
        }
        // The stored value's representation, which widens the array's kind: found
        // out by the store if the context doesn't know it (`Unknown`). See Note
        // [Array kinds].
        let ResumeArg::Type(stored) = (yield YieldOp::TypeofRk(c)) else { unreachable!() };
        let stored = stored.as_ltype();
        // A value of the array's known kind keeps it, and so does one of its
        // elements: the store needn't widen it, and an element changes no kind.
        let own = c & 0x100 == 0 && (yield YieldOp::IsElementOf(c, a)) == ResumeArg::Matched;
        // A mixed array stays mixed whatever is stored into it.
        let known = yield YieldOp::ArrayKind(a);
        let widen = !(own
            || known == ResumeArg::Type(CType::Type(LType::Unknown))
            || (stored != LType::Unknown && known == ResumeArg::Type(CType::Type(stored))));
        // Whether the value may be nil, which may shorten the array part. See
        // Note [Array length] in `vm`.
        let nil = matches!(stored, LType::Nil | LType::Unknown);
        // How the store widens the array's kind: not at all, by the value's
        // representation, known here, or by the value's found out.
        let how = match (widen, stored) {
            (false, _) => Widen::No,
            (true, LType::Unknown) => Widen::Decode,
            (true, stored) => Widen::Bit(stored),
        };
        if let (Some(Some(k)), ResumeArg::Matched) = (integer, &in_array) {
            windowed!(SetTableArray, [k: i32], [W: Widen, N: bool], |owner, state, base| (table, value) {
                let LValue::Table(tab) = table.unbox() else { unreachable!() };
                store_array::<W, N>(owner, &tab, integer_slot(k), value);
                // Last. See Note [Write barriers].
                tab.barrier_pending()
            } rejoin {
                let LValue::Table(tab) = table.unbox() else { unreachable!() };
                tab.barrier_slow();
            });
            windowed!(SetTableArrayK, [k: i32, value: u64], [W: Widen, N: bool], |owner, state, base| (table) {
                let LValue::Table(tab) = table.unbox() else { unreachable!() };
                // A constant's value lives as long as its prototype.
                let value = LBoxed::from_bits(value);
                store_array::<W, N>(owner, &tab, integer_slot(k), value);
                // Last. See Note [Write barriers].
                tab.barrier_pending()
            } rejoin {
                let LValue::Table(tab) = table.unbox() else { unreachable!() };
                tab.barrier_slow();
            });
            arg = yield YieldOp::ExecWindow(match constant {
                None => {
                    macro_rules! make { ($W:tt) => { if nil { Rc::new(SetTableArray::<$W, true>::new(k, &[a, c])) as Rc<dyn Window> } else { Rc::new(SetTableArray::<$W, false>::new(k, &[a, c])) as Rc<dyn Window> } } }
                    with_widen!(how, make)
                }
                Some(value) => {
                    macro_rules! make { ($W:tt) => { if nil { Rc::new(SetTableArrayK::<$W, true>::new(k, value, &[a])) as Rc<dyn Window> } else { Rc::new(SetTableArrayK::<$W, false>::new(k, value, &[a])) as Rc<dyn Window> } } }
                    with_widen!(how, make)
                }
            });
            if !own {
                yield YieldOp::Effect(Effect::ArrayStore(stored));
            }
        } else if let (Some(None), ResumeArg::Matched) = (integer, &in_array) {
            windowed!(SetTableInteger, [], [W: Widen, N: bool], |owner, state, base| (table, key, value) {
                let LValue::Table(tab) = table.unbox() else { unreachable!() };
                store_array::<W, N>(owner, &tab, integer_slot(key.as_int()), value);
                // Last. See Note [Write barriers].
                tab.barrier_pending()
            } rejoin {
                let LValue::Table(tab) = table.unbox() else { unreachable!() };
                tab.barrier_slow();
            });
            windowed!(SetTableIntegerK, [value: u64], [W: Widen, N: bool], |owner, state, base| (table, key) {
                let LValue::Table(tab) = table.unbox() else { unreachable!() };
                // A constant's value lives as long as its prototype.
                let value = LBoxed::from_bits(value);
                store_array::<W, N>(owner, &tab, integer_slot(key.as_int()), value);
                // Last. See Note [Write barriers].
                tab.barrier_pending()
            } rejoin {
                let LValue::Table(tab) = table.unbox() else { unreachable!() };
                tab.barrier_slow();
            });
            arg = yield YieldOp::ExecWindow(match constant {
                None => {
                    macro_rules! make { ($W:tt) => { if nil { Rc::new(SetTableInteger::<$W, true>::new(&[a, b, c])) as Rc<dyn Window> } else { Rc::new(SetTableInteger::<$W, false>::new(&[a, b, c])) as Rc<dyn Window> } } }
                    with_widen!(how, make)
                }
                Some(value) => {
                    macro_rules! make { ($W:tt) => { if nil { Rc::new(SetTableIntegerK::<$W, true>::new(value, &[a, b])) as Rc<dyn Window> } else { Rc::new(SetTableIntegerK::<$W, false>::new(value, &[a, b])) as Rc<dyn Window> } } }
                    with_widen!(how, make)
                }
            });
            if !own {
                yield YieldOp::Effect(Effect::ArrayStore(stored));
            }
        } else if let ResumeArg::Matched | ResumeArg::MatchedConst(_) = (yield YieldOp::GuardCType(b, CType::Number)) {
            // Any other number key, or one past the array part: through `set`.
            count_store!(array_stores);
            // A closure for each way of widening, which it knows as a constant.
            macro_rules! make {
                ($W:tt) => {
                    ResidualExec::new("settable_array", Rc::new(move |owner, state| {
                        let kb: LValue = match Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, b as u16) {
                            Ok(b) => LValue::from(b),
                            Err(lv) => lv.unbox(),
                        };
                        let Some(kb) = kb.as_f64() else { unreachable!() };
                        let kc: LBoxed = match Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, c as u16) {
                            Ok(c) => LBoxed::from(c),
                            Err(lv) => *lv,
                        };
                        let LValue::Table(mut t) = state.vals[state.base + a].unbox() else { unreachable!() };
                        t.set_widening::<$W>(owner, LBoxed::from_number(kb), kc, state.intern);
                    }))
                };
            }
            arg = yield YieldOp::Exec(with_widen!(how, make));
            // The exec writing any slot drops the kinds this function knows, but its
            // callers see only this. See Note [Call effects] in `specialize`.
            yield YieldOp::Effect(Effect::ArrayStore(stored));
        } else {
            // Hash part set
            arg = yield YieldOp::HashKey(a, b);
            if let ResumeArg::HashRef(hb, htype) = arg {
                count_store!(field_stores);
                let ResumeArg::Type(value_type) = (yield YieldOp::TypeofRk(c)) else { unreachable!() };
                let new_type = value_type.as_ltype();
                let retype = retype(new_type, htype);
                let expected = htype;
                if c & 0x100 == 0 {
                    arg = yield YieldOp::ExecWindow(match retype {
                        Retype::Same => Rc::new(SetTableHref::<{ Retype::Same }>::new(hb.0, expected, &[a, c])) as Rc<dyn Window>,
                        Retype::Known => Rc::new(SetTableHref::<{ Retype::Known }>::new(hb.0, expected, &[a, c])),
                        Retype::Unknown => Rc::new(SetTableHref::<{ Retype::Unknown }>::new(hb.0, expected, &[a, c])),
                    });
                } else {
                    let ResumeArg::Boxed(value) = (yield YieldOp::BoxedK(c & 0xff)) else { unreachable!() };
                    arg = yield YieldOp::ExecWindow(match retype {
                        Retype::Same => Rc::new(SetTableHrefK::<{ Retype::Same }>::new(hb.0, expected, value, &[a])) as Rc<dyn Window>,
                        Retype::Known => Rc::new(SetTableHrefK::<{ Retype::Known }>::new(hb.0, expected, value, &[a])),
                        Retype::Unknown => unreachable!("a constant of unknown type"),
                    });
                }
                arg = match retype {
                    Retype::Same => yield YieldOp::SetHazards(Some(a), Some(hb)),
                    // The table moves to a new epoch: the hash key's known type
                    // is the value's, if known. This also sets hazards.
                    Retype::Known | Retype::Unknown => yield YieldOp::UpdateHashRef(hb, new_type),
                };
            } else {
                arg = yield YieldOp::Exec(ResidualExec::new("settable_hash", Rc::new(move |owner, state| {
                    let kb: LBoxed = match Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, b as u16) {
                        Ok(b) => LBoxed::from(b),
                        Err(lv) => *lv,
                    };
                    let kb = LCanon::new(kb, state.intern);
                    let kc: LBoxed = match Vm::rk(state.clos.ro(owner).prototype, state.base, &state.vals, c as u16) {
                        Ok(c) => LBoxed::from(c),
                        Err(lv) => *lv,
                    };
                    let LValue::Table(t) = state.vals[state.base + a].unbox() else { unreachable!() };
                    // A field's type is a number's encoding. See Note [Field types].
                    let kc_type = kc.unbox().typeof_();
                    if let Some(existing) = t.rw(owner).insert_hash(kb, kc) {
                        info!("settable_hash with existing key {:?} {:?}", &existing, kc);
                        if existing.unbox().typeof_() != kc_type {
                            t.rw(owner).epoch += 1;
                        }
                    } else {
                        // Set new key, which implies keys that previously chained through the
                        // metatable or resolved to nil are invalidated.
                        t.rw(owner).epoch += 1;
                    }
                    // Last. See Note [Write barriers].
                    t.barrier_back();
                })));
                arg = yield YieldOp::SetHazards(None, None);
            }
        }
        arg
    }
}

pub fn emit_newtable(a: usize, b: usize, c: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Exec(ResidualExec::new("newtable", Rc::new(move |owner, state| {
            // TODO: properly decode the "floating point byte" size hints instead
            state.vals[state.base + a as usize] = LBoxed::box_lvalue(LValue::Table(Tc::new(Table::new(b as usize, c as usize))));
        })));
        yield YieldOp::SetTypes(vec![(a, LType::Table)]);
        yield YieldOp::CollectGarbage;
        arg
    }
}

pub fn emit_setlist(a: usize, b: usize, c: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        // We don't need to guard on LType::Table, because this instruction is only ever used for
        // table initialization, which means it is definitely a table and doesn't e.g. have a
        // metatable we have to chain to.
        arg = yield YieldOp::Exec(ResidualExec::new("setlist", Rc::new(move |owner, state| {
            match state.vals[state.base + a as usize].unbox() {
                LValue::Table(tab) => {
                    assert_ne!(c, 0);
                    tab.barrier_back();
                    let start = state.base + a as usize + 1;
                    let end = if b == 0 { state.top } else { start + b as usize };
                    // The first batch replaces the whole array part: its kind is
                    // its values', as are a later batch's added.
                    let mut kind = if c == 1 { 0 } else { tab.ro(owner).kind };
                    let src = state.vals[start..end].iter().map(|v| {
                        kind |= v.representation().bit();
                        *v
                    });
                    tab.rw(owner).array.splice(
                        (c as usize-1)*50..,
                        src
                    ).for_each(drop);
                    tab.rw(owner).kind = kind;
                    // See Note [Array length].
                    tab.rw(owner).trim();
                },
                _ => unreachable!(),
            };
        })));
        yield YieldOp::SetTypes(vec![(a, LType::Table)]);
        arg
    }
}

/// A numeric operand as a double, decoded from the integer encoding if `INT`.
/// See Note [Integers].
#[inline(always)]
unsafe fn number<'src, 'intern, const INT: bool>(v: LBoxed<'src, 'intern>, tag: u64) -> f64 {
    if INT {
        (unsafe { v.as_int() }) as f64
    } else {
        unsafe { v.as_double_tagged(tag) }
    }
}

/// The double op `OP` on `l` and `r`.
#[inline(always)]
unsafe fn arith_value<const OP: Opcode>(l: f64, r: f64) -> f64 {
    match OP {
        Opcode::ADD => l + r,
        Opcode::SUB => l - r,
        Opcode::MUL => l * r,
        Opcode::DIV => l / r,
        Opcode::MOD => crate::vm::lua_mod(l, r),
        Opcode::POW => l.powf(r),
        _ => unsafe { core::hint::unreachable_unchecked() },
    }
}

/// The double op `OP` on `l` and `r`, boxed. See Note [Arithmetic NaNs].
#[inline(always)]
unsafe fn arith<'src, 'intern, const OP: Opcode>(l: f64, r: f64, tag: u64) -> LBoxed<'src, 'intern> {
    unsafe { LBoxed::from_arith_tagged(arith_value::<OP>(l, r), tag) }
}

/// An integer op's result that doesn't fit the integer encoding, from its cold
/// path: the double op's, with a NaN canonical. Run by the interpreter, the cold
/// path is inlined after the test that failed, and LLVM may fold a NaN result
/// to its own constant, where the cold stencil computes x86's default NaN.
#[inline(always)]
unsafe fn overflowed<'src, 'intern, const OP: Opcode>(l: i32, r: i32) -> LBoxed<'src, 'intern> {
    LBoxed::from_double(unsafe { arith_value::<OP>(l as f64, r as f64) })
}

/// The integer op `OP`'s result, if it fits the integer encoding: it must be in
/// range, and neither -0 nor NaN. See Note [Integers].
#[inline(always)]
fn integer_op<const OP: Opcode>(l: i32, r: i32) -> Option<i32> {
    match OP {
        Opcode::ADD => l.checked_add(r),
        Opcode::SUB => l.checked_sub(r),
        // Zero times a negative number is -0.
        Opcode::MUL => l.checked_mul(r).filter(|&p| p != 0 || (l | r) >= 0),
        // Floored, as `lua_mod`. By zero, it is NaN.
        Opcode::MOD => (r != 0).then(|| {
            let m = l.wrapping_rem(r);
            if m != 0 && (m ^ r) < 0 { m + r } else { m }
        }),
        _ => unsafe { core::hint::unreachable_unchecked() },
    }
}

// The double ops on registers, `LI`/`RI` if in the integer encoding, and
// constants, `k` their value. Unchecked, so that no panic path follows the
// stencil's `become` and the copy can slice it off.
crate::window::windowed!(NumericRR, [], [OP: Opcode, LI: bool, RI: bool], |owner, state, base, tag| (lhs, rhs, out dest) {
    *dest = arith::<OP>(number::<LI>(lhs, tag), number::<RI>(rhs, tag), tag);
});
crate::window::windowed!(NumericKR, [k: f64], [OP: Opcode, RI: bool], |owner, state, base, tag| (rhs, out dest) {
    *dest = arith::<OP>(k, number::<RI>(rhs, tag), tag);
});
crate::window::windowed!(NumericRK, [k: f64], [OP: Opcode, LI: bool], |owner, state, base, tag| (lhs, out dest) {
    *dest = arith::<OP>(number::<LI>(lhs, tag), k, tag);
});

// Twins of the double ops on doubles, taking and giving them unboxed. See Note
// [Unboxed doubles] in `window_alloc`.
crate::window::windowed!(NumericRRX, [], [OP: Opcode], |owner, state, base| (f64 lhs, f64 rhs, out f64 dest) {
    *dest = arith_value::<OP>(lhs, rhs);
});
crate::window::windowed!(NumericKRX, [k: f64], [OP: Opcode], |owner, state, base| (f64 rhs, out f64 dest) {
    *dest = arith_value::<OP>(k, rhs);
});
crate::window::windowed!(NumericRKX, [k: f64], [OP: Opcode], |owner, state, base| (f64 lhs, out f64 dest) {
    *dest = arith_value::<OP>(lhs, k);
});
impl<const OP: Opcode> crate::window::Twin for NumericRR<OP, false, false> {
    fn twin(&self) -> Option<Rc<dyn Window>> {
        Some(Rc::new(NumericRRX::<OP>::new(Window::operands(self))))
    }
}
impl<const OP: Opcode> crate::window::Twin for NumericKR<OP, false> {
    fn twin(&self) -> Option<Rc<dyn Window>> {
        Some(Rc::new(NumericKRX::<OP>::new(self.k, Window::operands(self))))
    }
}
impl<const OP: Opcode> crate::window::Twin for NumericRK<OP, false> {
    fn twin(&self) -> Option<Rc<dyn Window>> {
        Some(Rc::new(NumericRKX::<OP>::new(self.k, Window::operands(self))))
    }
}

/// `NumericRR` for `opcode`, reading integer registers as `li`/`ri` say.
fn numeric_rr(opcode: Opcode, li: bool, ri: bool, operands: &[usize]) -> Rc<dyn Window> {
    match (li, ri) {
        (false, false) => dispatch_numeric_window!(opcode, NumericRR, [false, false], (operands)),
        (false, true) => dispatch_numeric_window!(opcode, NumericRR, [false, true], (operands)),
        (true, false) => dispatch_numeric_window!(opcode, NumericRR, [true, false], (operands)),
        (true, true) => dispatch_numeric_window!(opcode, NumericRR, [true, true], (operands)),
    }
}

/// `NumericKR` for `opcode`, reading an integer register if `ri`.
fn numeric_kr(opcode: Opcode, ri: bool, k: f64, operands: &[usize]) -> Rc<dyn Window> {
    match ri {
        false => dispatch_numeric_window!(opcode, NumericKR, [false], (k, operands)),
        true => dispatch_numeric_window!(opcode, NumericKR, [true], (k, operands)),
    }
}

/// `NumericRK` for `opcode`, reading an integer register if `li`.
fn numeric_rk(opcode: Opcode, li: bool, k: f64, operands: &[usize]) -> Rc<dyn Window> {
    match li {
        false => dispatch_numeric_window!(opcode, NumericRK, [false], (k, operands)),
        true => dispatch_numeric_window!(opcode, NumericRK, [true], (k, operands)),
    }
}

pub fn emit_numeric(opcode: Opcode, dest: usize, lhs: usize, rhs: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        let integer = ResumeArg::Type(CType::Type(LType::Integer));
        // --- Int Path --- See Note [Integers]. First, as finding out whether an
        // unknown operand is an integer finds out its type too.
        if matches!(opcode, Opcode::ADD | Opcode::SUB | Opcode::MUL | Opcode::MOD) {
            // The integer ops on registers and constants (`k`, their value), each with
            // its result in the integer encoding on its hot path, and in the double one,
            // as the double op would have it, on its cold path if it doesn't fit. See
            // Notes [Integers] and [Optimistic ops].
            let integers = integer_operands!(lhs, rhs);
            let (lk, rk) = ((lhs & 0x100) != 0, (rhs & 0x100) != 0);
            // The op, and whether its result can fail to fit. A constant operand is its
            // value, as `k`. luac folds two.
            let op = if !integers || (lk && rk) {
                None
            } else if lk {
                let ResumeArg::Integer(k) = (yield YieldOp::IntegerK(lhs & 0xff)) else { unreachable!() };
                crate::window::windowed!(IntegerKR, [k: i32], [OP: Opcode], |owner, state, base| (rhs, out dest) {
                    match integer_op::<OP>(k, rhs.as_int()) {
                        Some(n) => { *dest = LBoxed::from_int(n); false },
                        None => { core::intrinsics::cold_path(); true },
                    }
                } cold {
                    *dest = overflowed::<OP>(k, rhs.as_int());
                    1
                });
                Some((dispatch_integer_window!(opcode, IntegerKR, (k, &[rhs, dest])), true))
            } else if rk {
                let ResumeArg::Integer(k) = (yield YieldOp::IntegerK(rhs & 0xff)) else { unreachable!() };
                crate::window::windowed!(IntegerRK, [k: i32], [OP: Opcode], |owner, state, base| (lhs, out dest) {
                    match integer_op::<OP>(lhs.as_int(), k) {
                        Some(n) => { *dest = LBoxed::from_int(n); false },
                        None => { core::intrinsics::cold_path(); true },
                    }
                } cold {
                    *dest = overflowed::<OP>(lhs.as_int(), k);
                    1
                });
                // MOD by a constant other than zero always fits.
                crate::window::windowed!(ModRK, [k: i32], [], |owner, state, base| (lhs, out dest) {
                    *dest = LBoxed::from_int(crate::unchecked_unwrap(integer_op::<{ Opcode::MOD }>(lhs.as_int(), k)));
                });
                Some(match opcode == Opcode::MOD && k != 0 {
                    true => (Rc::new(ModRK::new(k, &[lhs, dest])) as Rc<dyn Window>, false),
                    false => (dispatch_integer_window!(opcode, IntegerRK, (k, &[lhs, dest])), true),
                })
            } else {
                crate::window::windowed!(IntegerRR, [], [OP: Opcode], |owner, state, base| (lhs, rhs, out dest) {
                    match integer_op::<OP>(lhs.as_int(), rhs.as_int()) {
                        Some(n) => { *dest = LBoxed::from_int(n); false },
                        None => { core::intrinsics::cold_path(); true },
                    }
                } cold {
                    *dest = overflowed::<OP>(lhs.as_int(), rhs.as_int());
                    1
                });
                Some((dispatch_integer_window!(opcode, IntegerRR, (&[lhs, rhs, dest])), true))
            };
            // As one step each way, as a guard of whether the result fits is
            // (Note [Subblocks]).
            match op {
                Some((op, true)) => {
                    let fits = yield YieldOp::OptimisticExec(op);
                    let ty = if fits == ResumeArg::Matched { LType::Integer } else { LType::Double };
                    yield YieldOp::SetCTypes(vec![(dest, CType::Type(ty))]);
                    return arg;
                },
                Some((op, false)) => {
                    yield YieldOp::Decided(true);
                    yield YieldOp::ExecWindow(op);
                    yield YieldOp::SetCTypes(vec![(dest, CType::Type(LType::Integer))]);
                    return arg;
                },
                None => {
                    yield YieldOp::Decided(false);
                },
            }
        }
        arg = yield YieldOp::GuardRk(lhs, LType::Table);
        if let ResumeArg::Matched | ResumeArg::MatchedConst(_) = arg {
            arg = yield YieldOp::GuardRk(rhs, LType::Table);
            if let ResumeArg::Matched | ResumeArg::MatchedConst(_) = arg {
                yield YieldOp::Exec(ResidualExec::new("numeric_table_table", Rc::new(move |owner, state| {
                    panic!();
                })));
                yield YieldOp::SetTypes(vec![(dest, LType::Unknown)]);
                return arg;
            }
        }
        // --- Number Path ---
        // Each register decoded from the encoding it is in. See Note [Integers].
        let larg = yield YieldOp::GuardCType(lhs, CType::Number);
        let rarg = yield YieldOp::GuardCType(rhs, CType::Number);
        let numbers = matches!(larg, ResumeArg::Matched | ResumeArg::MatchedConst(_))
            && matches!(rarg, ResumeArg::Matched | ResumeArg::MatchedConst(_));
        let (lint, rint) = if numbers { (integer_encoded!(lhs), integer_encoded!(rhs)) } else { (false, false) };
        let window = match (larg, rarg) {
            (ResumeArg::Matched, ResumeArg::Matched) => Some(numeric_rr(opcode, lint, rint, &[lhs, rhs, dest])),
            (ResumeArg::MatchedConst(lhsc), ResumeArg::MatchedConst(rhsc)) => {
                let ResumeArg::Number(l) = (yield YieldOp::NumberK(lhsc)) else { unreachable!() };
                let ResumeArg::Number(r) = (yield YieldOp::NumberK(rhsc)) else { unreachable!() };
                // A constant's NaN is canonicalized when it is captured (`NumberK`), as it
                // came from outside the encoding. See Note [Arithmetic NaNs].
                crate::window::windowed!(NumericKK, [kl: f64, kr: f64], [OP: Opcode], |owner, state, base, tag| (out dest) {
                    *dest = arith::<OP>(kl, kr, tag);
                });
                Some(dispatch_numeric_window!(opcode, NumericKK, [], (l, r, &[dest])))
            },
            (ResumeArg::MatchedConst(lhsc), ResumeArg::Matched) => {
                let ResumeArg::Number(k) = (yield YieldOp::NumberK(lhsc)) else { unreachable!() };
                Some(numeric_kr(opcode, rint, k, &[rhs, dest]))
            },
            (ResumeArg::Matched, ResumeArg::MatchedConst(rhsc)) => {
                let ResumeArg::Number(k) = (yield YieldOp::NumberK(rhsc)) else { unreachable!() };
                Some(numeric_rk(opcode, lint, k, &[lhs, dest]))
            },
            _ => None,
        };
        if let Some(window) = window {
            yield YieldOp::ExecWindow(window);
            yield YieldOp::SetCTypes(vec![(dest, CType::Type(LType::Double))]);
            return arg;
        }

        // --- Str Path ---
        arg = yield YieldOp::GuardRk(lhs, LType::String);
        if let ResumeArg::Matched | ResumeArg::MatchedConst(_) = arg {
            arg = yield YieldOp::GuardRk(rhs, LType::String);
            if let ResumeArg::Matched | ResumeArg::MatchedConst(_) = arg {
                yield YieldOp::Exec(ResidualExec::new("numeric_str_str", Rc::new(move |owner, state| {
                    //let RValue::Str(l) = &vals[lhs] else { unreachable!() };
                    //let RValue::Str(r) = &vals[rhs] else { unreachable!() };
                    //vals[dest] = RValue::Str(l.clone() + r);
                    unimplemented!()
                })));
                yield YieldOp::SetTypes(vec![(dest, LType::String)]);
                return arg;
            } else {
                debug!("fail 2");
            }
        } else {
            debug!("fail 1");
        }

        // --- Generic/Trap Fallback ---
        //panic!("Type mismatch trap");
        arg = yield YieldOp::Typeof(lhs);
        arg = yield YieldOp::Exec(ResidualExec::new("numeric_fail", Rc::new(move |owner, state| {
            panic!("numeric runtime type mismatch {:?} {:?}", arg, &state.vals)
        })));
        arg
    }
}

/// A compare's exit: 0 to take the jump, when the condition isn't `a`. `OP` is
/// a const param, so each stencil compares one way. Unchecked, so that no panic
/// path follows the stencil's `become`. See Note [Window exits] in `window`.
#[inline(always)]
unsafe fn compare_exit<const OP: Opcode, T: PartialOrd>(a: u8, l: T, r: T) -> usize {
    let cond = match OP {
        Opcode::EQ => l == r,
        Opcode::LT => l < r,
        Opcode::LE => l <= r,
        _ => unsafe { core::hint::unreachable_unchecked() },
    };
    if (cond as u8) != a { 0 } else { 1 }
}

// Compares of numbers: registers, `LI`/`RI` if in the integer encoding, and a
// constant, `k` its value.
crate::window::windowed!(select CompareRR, [a: u8], [OP: Opcode, LI: bool, RI: bool], |owner, state, base, tag| (lhs, rhs) {
    compare_exit::<OP, f64>(a, number::<LI>(lhs, tag), number::<RI>(rhs, tag))
});
crate::window::windowed!(select CompareKR, [a: u8, k: f64], [OP: Opcode, RI: bool], |owner, state, base, tag| (rhs) {
    compare_exit::<OP, f64>(a, k, number::<RI>(rhs, tag))
});
crate::window::windowed!(select CompareRK, [a: u8, k: f64], [OP: Opcode, LI: bool], |owner, state, base, tag| (lhs) {
    compare_exit::<OP, f64>(a, number::<LI>(lhs, tag), k)
});

// Twins of the compares of doubles, taking them unboxed. See Note [Unboxed
// doubles] in `window_alloc`.
crate::window::windowed!(select CompareRRX, [a: u8], [OP: Opcode], |owner, state, base| (f64 lhs, f64 rhs) {
    compare_exit::<OP, f64>(a, lhs, rhs)
});
crate::window::windowed!(select CompareKRX, [a: u8, k: f64], [OP: Opcode], |owner, state, base| (f64 rhs) {
    compare_exit::<OP, f64>(a, k, rhs)
});
crate::window::windowed!(select CompareRKX, [a: u8, k: f64], [OP: Opcode], |owner, state, base| (f64 lhs) {
    compare_exit::<OP, f64>(a, lhs, k)
});
impl<const OP: Opcode> crate::window::Twin for CompareRR<OP, false, false> {
    fn twin(&self) -> Option<Rc<dyn Window>> {
        Some(Rc::new(CompareRRX::<OP>::new(self.a, Window::operands(self))))
    }
}
impl<const OP: Opcode> crate::window::Twin for CompareKR<OP, false> {
    fn twin(&self) -> Option<Rc<dyn Window>> {
        Some(Rc::new(CompareKRX::<OP>::new(self.a, self.k, Window::operands(self))))
    }
}
impl<const OP: Opcode> crate::window::Twin for CompareRK<OP, false> {
    fn twin(&self) -> Option<Rc<dyn Window>> {
        Some(Rc::new(CompareRKX::<OP>::new(self.a, self.k, Window::operands(self))))
    }
}

// EQ of a double against a number constant `k` (its bits in the double
// encoding) other than ±0 or NaN: in the double encoding, equal numbers have
// equal bits but for ±0 (unequal bits) and NaN (equal to nothing), so it
// compares the bits.
crate::window::windowed!(select EqualBits, [a: u8, k: u64], [], |owner, state, base| (value) {
    if ((value.bits() == k) as u8) != a { 0 } else { 1 }
});

/// A double compared with the constant `k` by `opcode`: `EqualBits` when it can
/// be, else `CompareKR` or `CompareRK` (`k_left` if the constant is the left
/// operand).
fn compare_k(opcode: Opcode, int: bool, a: u8, k: f64, k_left: bool, operand: usize) -> Rc<dyn Window> {
    if opcode == Opcode::EQ && !int && k != 0.0 && !k.is_nan() {
        return Rc::new(EqualBits::new(a, LBoxed::from_double(k).bits(), &[operand]));
    }
    if k_left { compare_kr(opcode, int, a, k, &[operand]) } else { compare_rk(opcode, int, a, k, &[operand]) }
}

/// `CompareRR` for `opcode`, reading integer registers as `li`/`ri` say.
fn compare_rr(opcode: Opcode, li: bool, ri: bool, a: u8, operands: &[usize]) -> Rc<dyn Window> {
    match (li, ri) {
        (false, false) => dispatch_compare_window!(opcode, CompareRR, [false, false], (a, operands)),
        (false, true) => dispatch_compare_window!(opcode, CompareRR, [false, true], (a, operands)),
        (true, false) => dispatch_compare_window!(opcode, CompareRR, [true, false], (a, operands)),
        (true, true) => dispatch_compare_window!(opcode, CompareRR, [true, true], (a, operands)),
    }
}

/// `CompareKR` for `opcode`, reading an integer register if `ri`.
fn compare_kr(opcode: Opcode, ri: bool, a: u8, k: f64, operands: &[usize]) -> Rc<dyn Window> {
    match ri {
        false => dispatch_compare_window!(opcode, CompareKR, [false], (a, k, operands)),
        true => dispatch_compare_window!(opcode, CompareKR, [true], (a, k, operands)),
    }
}

/// `CompareRK` for `opcode`, reading an integer register if `li`.
fn compare_rk(opcode: Opcode, li: bool, a: u8, k: f64, operands: &[usize]) -> Rc<dyn Window> {
    match li {
        false => dispatch_compare_window!(opcode, CompareRK, [false], (a, k, operands)),
        true => dispatch_compare_window!(opcode, CompareRK, [true], (a, k, operands)),
    }
}

/// Lua's raw equality of two values.
#[inline(always)]
fn raw_equal<'s, 'i>(l: LBoxed<'s, 'i>, r: LBoxed<'s, 'i>) -> bool {
    // A value other than a number is equal to one with the same bits; a NaN is
    // not, and equal numbers or strings can have different bits.
    (l.bits() == r.bits() && l.bits() & LBoxed::NUMBER_TAG == 0) || unboxed_equal(l, r)
}

/// `raw_equal`'s comparison of the values themselves. Out of line: its match is
/// a jump table, which a stencil can't hold.
#[inline(never)]
fn unboxed_equal<'s, 'i>(l: LBoxed<'s, 'i>, r: LBoxed<'s, 'i>) -> bool {
    l.unbox() == r.unbox()
}

pub fn emit_compare(opcode: Opcode, a: u8, b: usize, c: usize, pc: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        // Integers compare as integers, and each other register is decoded from
        // the encoding it is in. See Note [Integers].
        let integers = integer_operands!(b, c);
        let larg = yield YieldOp::GuardCType(b, CType::Number);
        let rarg = yield YieldOp::GuardCType(c, CType::Number);
        let numbers = matches!(larg, ResumeArg::Matched | ResumeArg::MatchedConst(_))
            && matches!(rarg, ResumeArg::Matched | ResumeArg::MatchedConst(_));
        let (lint, rint) = if numbers { (integer_encoded!(b), integer_encoded!(c)) } else { (false, false) };

        let lnil = yield YieldOp::GuardRk(b, LType::Nil);
        let rnil = yield YieldOp::GuardRk(c, LType::Nil);

        arg = yield YieldOp::GetBlock(pc);
        let ResumeArg::BlockId(fallthrough) = arg else { unreachable!() };
        arg = yield YieldOp::GetBlock((pc as isize + 1 as isize) as usize);
        let ResumeArg::BlockId(taken) = arg else { unreachable!() };

        // Compares of integers, a constant one its value `k`: known to be before, or
        // both registers found in the integer encoding by the guards above. See Note
        // [Integers].
        match (larg, rarg) {
            (ResumeArg::Matched, ResumeArg::Matched) if integers || (lint && rint) => {
                crate::window::windowed!(select CompareIntRR, [a: u8], [OP: Opcode], |owner, state, base| (lhs, rhs) {
                    compare_exit::<OP, i32>(a, lhs.as_int(), rhs.as_int())
                });
                arg = yield YieldOp::ExecWindow(dispatch_compare_window!(opcode, CompareIntRR, [], (a, &[b, c])));
            },
            (ResumeArg::Matched, ResumeArg::Matched) => {
                arg = yield YieldOp::ExecWindow(compare_rr(opcode, lint, rint, a, &[b, c]));
            },
            (ResumeArg::MatchedConst(rb), ResumeArg::Matched) if integers => {
                let ResumeArg::Integer(k) = (yield YieldOp::IntegerK(rb)) else { unreachable!() };
                crate::window::windowed!(select CompareIntKR, [a: u8, k: i32], [OP: Opcode], |owner, state, base| (rhs) {
                    compare_exit::<OP, i32>(a, k, rhs.as_int())
                });
                arg = yield YieldOp::ExecWindow(dispatch_compare_window!(opcode, CompareIntKR, [], (a, k, &[c])));
            },
            (ResumeArg::MatchedConst(rb), ResumeArg::Matched) => {
                let ResumeArg::Number(k) = (yield YieldOp::NumberK(rb)) else { unreachable!() };
                arg = yield YieldOp::ExecWindow(compare_k(opcode, rint, a, k, true, c));
            },
            (ResumeArg::Matched, ResumeArg::MatchedConst(rc)) if integers => {
                let ResumeArg::Integer(k) = (yield YieldOp::IntegerK(rc)) else { unreachable!() };
                crate::window::windowed!(select CompareIntRK, [a: u8, k: i32], [OP: Opcode], |owner, state, base| (lhs) {
                    compare_exit::<OP, i32>(a, lhs.as_int(), k)
                });
                arg = yield YieldOp::ExecWindow(dispatch_compare_window!(opcode, CompareIntRK, [], (a, k, &[b])));
            },
            (ResumeArg::Matched, ResumeArg::MatchedConst(rc)) => {
                let ResumeArg::Number(k) = (yield YieldOp::NumberK(rc)) else { unreachable!() };
                arg = yield YieldOp::ExecWindow(compare_k(opcode, lint, a, k, false, b));
            },
            (ResumeArg::MatchedConst(rb), ResumeArg::MatchedConst(rc)) => {
                let ResumeArg::Number(l) = (yield YieldOp::NumberK(rb)) else { unreachable!() };
                let ResumeArg::Number(r) = (yield YieldOp::NumberK(rc)) else { unreachable!() };
                let cond = match opcode {
                    Opcode::EQ => l == r,
                    Opcode::LT => l < r,
                    Opcode::LE => l <= r,
                    _ => unreachable!(),
                };
                // Statically decided, as `select` would.
                yield YieldOp::Jump(if (cond as u8) != a { taken } else { fallthrough });
            },
            (larg, rarg) if opcode == Opcode::EQ && !matches!((&lnil, &rnil), (ResumeArg::Matched | ResumeArg::MatchedConst(_), _) | (_, ResumeArg::Matched | ResumeArg::MatchedConst(_))) => {
                // Raw equality of values of any types, a constant operand's boxed
                // value a hole.
                crate::window::windowed!(select EqualRR, [a: u8], [], |owner, state, base| (lhs, rhs) {
                    if (raw_equal(lhs, rhs) as u8) != a { 0 } else { 1 }
                });
                crate::window::windowed!(select EqualRK, [a: u8, k: u64], [], |owner, state, base| (lhs) {
                    if (raw_equal(lhs, LBoxed::from_bits(k)) as u8) != a { 0 } else { 1 }
                });
                const RK: usize = 256;
                let window: Rc<dyn Window> = match (b >= RK, c >= RK) {
                    (false, false) => Rc::new(EqualRR::new(a, &[b, c])),
                    (true, false) => {
                        let ResumeArg::Boxed(k) = (yield YieldOp::BoxedK(b - RK)) else { unreachable!() };
                        Rc::new(EqualRK::new(a, k, &[c]))
                    },
                    (false, true) => {
                        let ResumeArg::Boxed(k) = (yield YieldOp::BoxedK(c - RK)) else { unreachable!() };
                        Rc::new(EqualRK::new(a, k, &[b]))
                    },
                    (true, true) => unimplemented!("equality of two constants"),
                };
                arg = yield YieldOp::ExecWindow(window);
            },
            (larg, rarg) => {
                if opcode != Opcode::EQ {
                    unimplemented!("ordering a nil (an error, or a metamethod)");
                }
                let equal = match (&lnil, &rnil) {
                    (ResumeArg::Matched | ResumeArg::MatchedConst(_), ResumeArg::Matched | ResumeArg::MatchedConst(_)) => true,
                    (ResumeArg::Matched | ResumeArg::MatchedConst(_), _) | (_, ResumeArg::Matched | ResumeArg::MatchedConst(_)) => false,
                    _ => unimplemented!(),
                };
                // Statically decided: take the jump when the condition isn't `a`,
                // as `select` does.
                yield YieldOp::Jump(if (equal as u8) != a { taken } else { fallthrough });
            }
        }
        arg = yield YieldOp::Select(vec![("taken", taken), ("fallthrough", fallthrough)]);
        arg
    }
}

pub fn emit_test(a: usize, c: u16, pc: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        // TODO: __eq metatable?
        // The targets are found after the guards, so they're versioned for what
        // the guards found out.
        let (fallthrough, taken) = (pc, pc + 1);
        arg = yield YieldOp::Guard(a, LType::Bool);
        if let ResumeArg::Matched = arg {
            // Exit 1, the fallthrough, when the guarded bool is `C`.
            windowed!(select TestBool, [], [C: bool], |owner, state, base| (value) {
                ((value.bits() == LBoxed::VALUE_TRUE) == C) as usize
            });
            arg = yield YieldOp::ExecWindow(if c != 0 {
                Rc::new(TestBool::<true>::new(&[a]))
            } else {
                Rc::new(TestBool::<false>::new(&[a]))
            });
            let ResumeArg::BlockId(fallthrough) = (yield YieldOp::GetBlock(fallthrough)) else { unreachable!() };
            let ResumeArg::BlockId(taken) = (yield YieldOp::GetBlock(taken)) else { unreachable!() };
            arg = yield YieldOp::Select(vec![("taken", taken), ("fallthrough", fallthrough)]);
            return arg
        }
        // The next instruction (a jump) runs when R(A)'s truthiness is C, else it
        // is skipped. Nil is false, and everything else true.
        arg = yield YieldOp::Guard(a, LType::Nil);
        let truthy = arg != ResumeArg::Matched;
        let ResumeArg::BlockId(target) = (yield YieldOp::GetBlock(if truthy == (c != 0) { fallthrough } else { taken })) else { unreachable!() };
        arg = yield YieldOp::Jump(target);
        arg
    }
}

pub fn emit_jmp(sbx: i32, pc: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::GetBlock(((pc as isize) + sbx as isize) as usize);
        let ResumeArg::BlockId(target) = arg else { unreachable!() };
        arg = yield YieldOp::Jump(target);
        arg
    }
}

pub fn emit_unm(a: usize, b: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::GuardCType(b, CType::Number);
        let (ResumeArg::Matched | ResumeArg::MatchedConst(_)) = arg else {
            unimplemented!("__unm metatable");
        };
        arg = yield YieldOp::Exec(ResidualExec::new("unm", Rc::new(move |owner, state| {
            let res = match state.vals[state.base + b as usize].unbox() {
                // TODO: metatables
                LValue::Integer(_) | LValue::Double(_) => LValue::number(-state.vals[state.base + b as usize].as_number().unwrap()),
                _ => unimplemented!(),
            };
            state.vals[state.base + a as usize] = LBoxed::box_lvalue(res);
        })));
        yield YieldOp::SetCTypes(vec![(a, CType::Number)]);
        arg
    }
}

pub fn emit_len(a: usize, b: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Guard(b, LType::String);
        if ResumeArg::Matched == arg {
            arg = yield YieldOp::Exec(ResidualExec::new("len_str", Rc::new(move |owner, state| {
                let n = match state.vals[state.base + b].unbox() {
                    LValue::OwnedString(s) => s.as_slice().len(),
                    LValue::InternedString(s) => s.as_bytes().len(),
                    _ => unreachable!(),
                };
                state.vals[state.base + a] = LBoxed::box_lvalue(LValue::number(n as _));
            })));
            yield YieldOp::SetCTypes(vec![(a, CType::Number)]);
            return arg;
        }
        arg = yield YieldOp::Guard(b, LType::Table);
        if ResumeArg::Matched == arg {
            // TODO: __len metamethod
            arg = yield YieldOp::Exec(ResidualExec::new("len_tab", Rc::new(move |owner, state| {
                let LValue::Table(b) = state.vals[state.base + b].unbox() else { unreachable!() };
                let n = b.ro(owner).array.len();
                state.vals[state.base + a] = LBoxed::box_lvalue(LValue::number(n as _));
            })));
            yield YieldOp::SetCTypes(vec![(a, CType::Number)]);
            return arg;
        } else {
            unimplemented!("__len metamethod")
        }

        arg
    }
}

pub fn emit_concat(a: usize, b: usize, c: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Exec(ResidualExec::new("concat", Rc::new(move |owner, state| {
            // The result is sized before it's written, so it's one allocation, with each
            // operand copied into it once. Operands that aren't strings are converted first.
            let operands = &state.vals[state.base + b..=state.base + c];
            let mut converted: SmallVec<[Vec<u8>; 2]> = SmallVec::new();
            let mut len = 0;
            for operand in operands {
                len += match operand.unbox() {
                    LValue::OwnedString(g) => g.len(),
                    LValue::InternedString(is) => is.as_bytes().len(),
                    value => {
                        converted.push(value.string_bytes(owner));
                        converted.last().unwrap().len()
                    },
                };
            }
            let mut converted = converted.iter();
            let s = crate::gc::Gc::build(len, |w| {
                for operand in operands {
                    match operand.unbox() {
                        LValue::OwnedString(g) => w.push(g.as_slice()),
                        LValue::InternedString(is) => w.push(is.as_bytes()),
                        _ => w.push(converted.next().unwrap()),
                    }
                }
            });
            debug!("concat {:?}", String::from_utf8_lossy(s.as_slice()));
            state.vals[state.base + a as usize] = LBoxed::box_lvalue(LValue::OwnedString(s));
        })));
        arg = yield YieldOp::SetTypes(vec![(a, LType::String)]);
        // It allocates. See Note [Block safepoints].
        yield YieldOp::CollectGarbage;
        arg
    }
}

/// `R(A) := not R(B)`.
pub fn emit_not(a: usize, b: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        windowed!(Not, [], [], |owner, state, base| (value, out dest) {
            *dest = LBoxed::from_bool(value.bits() == LBoxed::VALUE_NIL || value.bits() == LBoxed::VALUE_FALSE);
        });
        yield YieldOp::ExecWindow(Rc::new(Not::new(&[b, a])));
        yield YieldOp::SetTypes(vec![(a, LType::Bool)]);
        arg
    }
}

/// `if R(B)'s truthiness is C then R(A) := R(B) else skip the next instruction`
/// (a jump). `pc` is the next instruction's.
pub fn emit_testset(a: usize, b: usize, c: u16, pc: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Guard(b, LType::Bool);
        if let ResumeArg::Matched = arg {
            // Exit 1, the fallthrough, when the guarded bool is `C`, and then R(A)
            // is it.
            windowed!(select TestSetBool, [], [C: bool], |owner, state, base| (value, inout dest) {
                let set = (value.bits() == LBoxed::VALUE_TRUE) == C;
                if set {
                    *dest = value;
                }
                set as usize
            });
            yield YieldOp::ExecWindow(if c != 0 {
                Rc::new(TestSetBool::<true>::new(&[b, a]))
            } else {
                Rc::new(TestSetBool::<false>::new(&[b, a]))
            });
            // R(A) is a bool if it was one before, whichever path is taken.
            let ResumeArg::Type(before) = (yield YieldOp::Typeof(a)) else { unreachable!() };
            let after = if before.as_ltype() == LType::Bool { LType::Bool } else { LType::Unknown };
            yield YieldOp::SetTypes(vec![(a, after)]);
            arg = yield YieldOp::GetBlock(pc);
            let ResumeArg::BlockId(fallthrough) = arg else { unreachable!() };
            arg = yield YieldOp::GetBlock(pc + 1);
            let ResumeArg::BlockId(taken) = arg else { unreachable!() };
            arg = yield YieldOp::Select(vec![("taken", taken), ("fallthrough", fallthrough)]);
            return arg
        }
        // Nil is false, and everything else is true.
        arg = yield YieldOp::Guard(b, LType::Nil);
        let truthy = arg != ResumeArg::Matched;
        if truthy == (c != 0) {
            let ResumeArg::Type(t) = (yield YieldOp::Typeof(b)) else { unreachable!() };
            windowed!(TestSetMove, [], [], |owner, state, base| (from, out to) {
                *to = from;
            });
            yield YieldOp::ExecWindow(Rc::new(TestSetMove::new(&[b, a])));
            yield YieldOp::SetCTypes(vec![(a, t)]);
            arg = yield YieldOp::GetBlock(pc);
        } else {
            arg = yield YieldOp::GetBlock(pc + 1);
        }
        let ResumeArg::BlockId(target) = arg else { unreachable!() };
        arg = yield YieldOp::Jump(target);
        arg
    }
}

/// `R(A), ..., R(A+B-2) := the running vararg function's extra arguments`, or
/// with B = 0 all of them, the top just past them. `params` is how many fixed
/// parameters it has. See Note [Vararg frames] in
/// `vm`.
pub fn emit_vararg(a: usize, b: usize, params: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Exec(ResidualExec::new("vararg", Rc::new(move |owner, state| {
            state.vararg(owner, a, b, params);
        })));
        if b == 0 {
            yield YieldOp::Clobber(a);
        } else {
            yield YieldOp::SetTypes((a..a + b - 1).map(|slot| (slot, LType::Unknown)).collect());
        }
        arg
    }
}

/// Close every upvalue open into a slot from R(A) up.
pub fn emit_close(a: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Exec(ResidualExec::new("close", Rc::new(move |owner, state| {
            let from = state.base + a;
            state.close_upvalues_from(owner, from);
        })));
        arg
    }
}

pub fn emit_move(dest: usize, src: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Typeof(src);
        if let ResumeArg::Type(t) = arg.clone() {
            windowed!(Move, [], [], |owner, state, base| (from, out to) {
                *to = from;
            });
            yield YieldOp::ExecWindow(Rc::new(Move::new(&[src, dest])));
            // TODO: track references? see PyLBBV
            debug!("move {} = {} {:?}", dest, src, t);
            yield YieldOp::SetCTypes(vec![(dest, t)]);
        } else {
            unreachable!();
        }
        return arg;
    }
}

pub fn emit_getupval(a: usize, b: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        windowed!(GetUpval, [index: usize], [], |owner, state, base| (out dest) {
            let upval = match state.clos.ro(owner).upvalues[index].deref().ro(owner) {
                Upvalue::Open(o) => {
                    // The running closure's upvalues were captured by an enclosing
                    // function, so an open one is a slot of an enclosing frame, not
                    // one of this frame's (which the window may cache).
                    debug_assert!(*o < state.base, "open upvalue in the running frame");
                    state.vals[*o as usize]
                },
                Upvalue::Closed(c) => *c.ro(owner),
            };
            debug!("upval {:?}", &upval);
            *dest = upval;
        });
        // An upvalue the context knows holds a native is that constant, not a
        // read. See Note [Fragile information].
        windowed!(NativeUpval, [bits: u64, index: usize], [], |owner, state, base| (out dest) {
            #[cfg(debug_assertions)]
            {
                let held = match state.clos.ro(owner).upvalues[index].deref().ro(owner) {
                    Upvalue::Open(o) => state.vals[*o as usize],
                    Upvalue::Closed(c) => *c.ro(owner),
                };
                assert_eq!(held.bits(), bits, "fragile information: another native was assumed");
            }
            let _ = index;
            *dest = LBoxed::from_bits(bits);
        });
        // One a slot is known to still hold is a move from that slot, or
        // nothing if it is the destination.
        windowed!(HeldUpval, [index: usize], [], |owner, state, base| (from, out to) {
            #[cfg(debug_assertions)]
            {
                let held = match state.clos.ro(owner).upvalues[index].deref().ro(owner) {
                    Upvalue::Open(o) => state.vals[*o as usize],
                    Upvalue::Closed(c) => *c.ro(owner),
                };
                assert_eq!(held.bits(), from.bits(), "fragile information: the slot was assumed to hold the upvalue");
            }
            let _ = index;
            *to = from;
        });
        match yield YieldOp::UpvalueKnown(b) {
            ResumeArg::Boxed(bits) => {
                yield YieldOp::ExecWindow(Rc::new(NativeUpval::new(bits, b, &[a])));
            },
            ResumeArg::Integer(slot) if slot as usize == a => {},
            ResumeArg::Integer(slot) => {
                yield YieldOp::ExecWindow(Rc::new(HeldUpval::new(b, &[slot as usize, a])));
            },
            _ => {
                yield YieldOp::ExecWindow(Rc::new(GetUpval::new(b, &[a])));
            },
        }
        arg = yield YieldOp::LoadUpvalue(a, b);
        return arg;
    }
}

/// `R(A) := closure(KPROTO[Bx], R(A), ... ,R(A+n))`: a closure of the function's
/// prototype `bx`, its upvalues from the `upvalues` pseudo-instructions after it.
/// Continues at `next`, the instruction after them. See Note [Captured slots].
pub fn emit_closure(a: usize, bx: usize, upvalues: Vec<(Opcode, usize)>, next: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        let skip = !upvalues.is_empty();
        let upvalues = upvalues.clone();
        arg = yield YieldOp::Exec(ResidualExec::new("closure", Rc::new(move |owner, state| {
            let proto = unsafe { &(&(*state.clos.ro(owner).prototype).prototypes.items)[bx] };
            let mut fresh = LClosure::new(proto as *const _);
            for &(from, b) in upvalues.iter() {
                let cell = if from == Opcode::MOVE {
                    let slot = state.base + b;
                    let open = state.upvals.iter().find(|(upval, _)| matches!(upval, Upvalue::Open(o) if *o == slot));
                    match open {
                        Some((_, uses)) => uses[0].clone(),
                        None => {
                            let cell = Tc::new(Upvalue::Open(slot));
                            state.upvals.push((Upvalue::Open(slot), vec![cell.clone()].into()));
                            cell
                        }
                    }
                } else {
                    state.clos.ro(owner).upvalues[b].clone()
                };
                fresh.upvalues.push(cell);
            }
            state.vals[state.base + a] = LBoxed::box_lvalue(LValue::LClosure(Tc::new(fresh)));
        })));
        yield YieldOp::SetTypes(vec![(a, LType::Closure)]);
        yield YieldOp::CollectGarbage;
        if skip {
            arg = yield YieldOp::GetBlock(next);
            let ResumeArg::BlockId(target) = arg else { unreachable!() };
            arg = yield YieldOp::Jump(target);
        }
        arg
    }
}

/// Store into a closed upvalue's cell. Out of line: its write barrier's marking
/// dispatches through a jump table, which a stencil can't hold.
#[inline(never)]
fn set_closed<'src, 'intern>(owner: &mut Owner, cell: Tc<LBoxed<'src, 'intern>>, value: LBoxed<'src, 'intern>) {
    cell.replace(owner, value);
}

/// `UpValue[B] := R(A)`. See Note [Captured slots].
pub fn emit_setupval(a: usize, b: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        // A closed upvalue is stored out of line.
        windowed!(SetUpval, [index: usize], [], |owner, state, base| (value) {
            let upval = state.clos.ro(owner).upvalues[index].deref().ro(owner).clone();
            match upval {
                Upvalue::Open(o) => {
                    debug_assert!(o < state.base, "open upvalue in the running frame");
                    state.vals[o] = value;
                    false
                },
                Upvalue::Closed(_) => true,
            }
        } rejoin {
            let upval = state.clos.ro(owner).upvalues[index].deref().ro(owner).clone();
            let Upvalue::Closed(c) = upval else { unreachable!("an upvalue closed by its store") };
            set_closed(owner, c, value);
        });
        arg = yield YieldOp::ExecWindow(Rc::new(SetUpval::new(b, &[a])));
        yield YieldOp::Effect(Effect::SetUpvalue(b));
        arg
    }
}

/// `R(A+1) := R(B); R(A) := R(B)[RK(C)]`: the move first, as the method's load
/// overwrites `R(B)` when `B` is `A`.
pub fn emit_self(a: usize, b: usize, c: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        let mut moveself = emit_move(a + 1, b);
        drain!(moveself, arg);
        let mut getmem = emit_gettable(a, b, c);
        drain!(getmem, arg);
        ResumeArg::Start
    }
}

pub fn emit_forprep(a: usize, sbx: i32, pc: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        debug!("forprep {a} {sbx} {pc}");
        // An integer loop's index, limit and step are integers: find out which
        // are. See Note [Integers].
        for slot in a..a + 3 {
            yield YieldOp::GuardCType(slot, CType::Type(LType::Integer));
        }
        let mut sub = emit_numeric(Opcode::SUB, a, a, a + 2);
        drain!(sub, arg);
        arg = yield YieldOp::GetBlock(((pc as isize) + sbx as isize) as usize);
        let ResumeArg::BlockId(target) = arg else { unreachable!() };
        yield YieldOp::Jump(target);
        return arg;
    }
}

// FORLOOP's test, reading its index, limit and step in the integer encoding as
// `II`, `LI` and `SI` say (see Note [Integers]), and comparing them as integers
// if all are.
//
// Lua sets the loop variable only when the loop continues, but it is local to
// the loop's body: after the loop exits nothing reads it before writing it,
// and a closure capturing it has it closed (`CLOSE`) at the end of each
// iteration, before this runs. So it is set on exit too, and the op needn't
// read its old value.
crate::window::windowed!(select ForLoop, [], [II: bool, LI: bool, SI: bool], |owner, state, base, tag| (idx, limit, step, out var) {
    let comp = if II && LI && SI {
        let (nidx, nlimit, nstep) = (idx.as_int(), limit.as_int(), step.as_int());
        if nstep < 0 { nlimit <= nidx } else { nidx <= nlimit }
    } else {
        let (nidx, nlimit, nstep) = (number::<II>(idx, tag), number::<LI>(limit, tag), number::<SI>(step, tag));
        if nstep < 0.0 { nlimit <= nidx } else { nidx <= nlimit }
    };
    *var = idx;
    if comp { 0 } else { 1 }
});

/// `ForLoop`, reading integers as `ii`, `li` and `si` say.
fn for_loop(ii: bool, li: bool, si: bool, operands: &[usize]) -> Rc<dyn Window> {
    match (ii, li, si) {
        (false, false, false) => Rc::new(ForLoop::<false, false, false>::new(operands)),
        (false, false, true) => Rc::new(ForLoop::<false, false, true>::new(operands)),
        (false, true, false) => Rc::new(ForLoop::<false, true, false>::new(operands)),
        (false, true, true) => Rc::new(ForLoop::<false, true, true>::new(operands)),
        (true, false, false) => Rc::new(ForLoop::<true, false, false>::new(operands)),
        (true, false, true) => Rc::new(ForLoop::<true, false, true>::new(operands)),
        (true, true, false) => Rc::new(ForLoop::<true, true, false>::new(operands)),
        (true, true, true) => Rc::new(ForLoop::<true, true, true>::new(operands)),
    }
}

pub fn emit_forloop(a: usize, sbx: i32, pc: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        debug!("forloop {a} {sbx} {pc}");
        debug!("{} {}", a, sbx);
        let mut add = emit_numeric(Opcode::ADD, a, a, a + 2);
        drain!(add, arg);

        // Each decoded from the encoding it is in. See Note [Integers].
        let idx_number = yield YieldOp::GuardCType(a, CType::Number);
        let limit_number = yield YieldOp::GuardCType(a + 1, CType::Number);
        let step_number = yield YieldOp::GuardCType(a + 2, CType::Number);

        match (idx_number, limit_number, step_number) {
            (ResumeArg::Matched, ResumeArg::Matched, ResumeArg::Matched) => {
                let (ii, li, si) = (integer_encoded!(a), integer_encoded!(a + 1), integer_encoded!(a + 2));
                yield YieldOp::ExecWindow(for_loop(ii, li, si, &[a, a + 1, a + 2, a + 3]));
                let ResumeArg::Type(t) = (yield YieldOp::Typeof(a)) else { unreachable!() };
                yield YieldOp::SetCTypes(vec![(a + 3, t)]);
            },
            _ => {
                yield YieldOp::Exec(ResidualExec::new("forloop_other", Rc::new(move |owner, state| {
                    panic!("forloop induction variable metamethod");
                })));
                yield YieldOp::SetTypes(vec![(a + 3, LType::Unknown)]);
            },
        }
        // The targets are versioned for the context the op leaves, with the loop
        // variable's type set.
        // TODO: `comp` metamethods? which may invalidate the types that our resolved
        // blocks are compatible for? i think they're fine because they're on the stack whatever
        arg = yield YieldOp::GetBlock(pc);
        let ResumeArg::BlockId(fallthrough) = arg else { unreachable!() };
        arg = yield YieldOp::GetBlock((pc as isize + sbx as isize) as usize);
        let ResumeArg::BlockId(taken) = arg else { unreachable!() };
        // For debug tracing, statically document that we have two outgoing edges
        yield YieldOp::Select(vec![("forloop_start", taken), ("forloop_finish", fallthrough)]);
        arg
    }
}

pub fn emit_call(a: usize, b: usize, c: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        arg = yield YieldOp::Guard(a, LType::Closure);
        if arg != ResumeArg::Matched {
            arg = yield YieldOp::Exec(ResidualExec::new("call_meta", Rc::new(move |owner, state| {
                debug!("??? {arg:?}");
                panic!("call metamethod {} {:?} {:?}", a, &state.vals, &state.vals[state.base + a])
            })));
            return arg;
        }
        // A native's window op assumes its arguments' type: guard them to it, so an
        // argument of unknown type is discovered, and the call can run as the op if
        // it has it. See Note [Native windows].
        if let ResumeArg::WindowArgs(end, args) = (yield YieldOp::NativeWindowArgs(a, b, c)) {
            for slot in a + 1..end {
                yield YieldOp::GuardCType(slot, args.clone());
            }
        }
        // TODO: track concrete function targets at the type level, and emit a YieldOp::Dispatch
        // guard here for specializing the call + return continuation for each one.
        // The specializer ends the instruction at the call, and clears the hazards
        // itself: the generator isn't resumed after it.
        arg = yield YieldOp::Call(CallTarget::Dynamic(a, b, c));
        arg
    }
}

/// A generic `for`'s step: `R(A+3), ..., R(A+2+C) := R(A)(R(A+1), R(A+2))`; then
/// if R(A+3) isn't nil, `R(A+2) := R(A+3)`, else skip the next instruction (the
/// jump back to the loop's body). `pc` is the next instruction's.
pub fn emit_tforloop(a: usize, c: usize, pc: usize) -> impl Coroutine<ResumeArg, Yield = YieldOp, Return = ResumeArg> + Clone + Unpin {
    #[coroutine]
    move |mut arg: ResumeArg| {
        windowed!(ForInMove, [], [], |owner, state, base| (from, out to) {
            *to = from;
        });
        // The iterator, its state and the control variable, called.
        let f = a + 3;
        for i in 0..3 {
            let ResumeArg::Type(t) = (yield YieldOp::Typeof(a + i)) else { unreachable!() };
            yield YieldOp::ExecWindow(Rc::new(ForInMove::new(&[a + i, f + i])));
            yield YieldOp::SetCTypes(vec![(f + i, t)]);
        }
        arg = yield YieldOp::Guard(f, LType::Closure);
        if arg != ResumeArg::Matched {
            arg = yield YieldOp::Exec(ResidualExec::new("call_meta", Rc::new(move |owner, state| {
                panic!("call metamethod {} {:?}", f, &state.vals[state.base + f])
            })));
            return arg;
        }
        // As a call's. See Note [Native windows].
        if let ResumeArg::WindowArgs(end, args) = (yield YieldOp::NativeWindowArgs(f, 3, c + 1)) {
            for slot in f + 1..end {
                yield YieldOp::GuardCType(slot, args.clone());
            }
        }
        yield YieldOp::CallResume(CallTarget::Dynamic(f, 3, c + 1));
        arg = yield YieldOp::Guard(f, LType::Nil);
        if arg == ResumeArg::Matched {
            arg = yield YieldOp::GetBlock(pc + 1);
            let ResumeArg::BlockId(done) = arg else { unreachable!() };
            arg = yield YieldOp::Jump(done);
            return arg;
        }
        let ResumeArg::Type(t) = (yield YieldOp::Typeof(f)) else { unreachable!() };
        yield YieldOp::ExecWindow(Rc::new(ForInMove::new(&[f, a + 2])));
        yield YieldOp::SetCTypes(vec![(a + 2, t)]);
        arg
    }
}

/// The array part slot of a `CType::Type(LType::Integer)` key. Keys below 1 wrap past any
/// array part.
#[inline(always)]
fn integer_slot(i: i32) -> usize {
    (i as i64 - 1) as usize
}
