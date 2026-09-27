//! The parts of Lua's standard library (and LuaJIT's `bit`, `table.new` and
//! `table.clear` extensions) that lunacy has, as natives in the global table.
//! See Note [Library natives].

use std::cell::RefCell;
use std::io::Write;

use indexmap::IndexMap;
use smallvec::{smallvec, SmallVec};

use crate::gc::Gc;
use crate::lboxed::LBoxed;
use crate::vm::{FVec, IStr, InternString, InternedHasher, LType, LValue, NClosure, Table, Tc};
use crate::vm::NativeOp;

// Note [Library natives]
// ~~~~~~~~~~~~~~~~~~~~~~
// A native gets its arguments and the slots for its results as two views of the
// stack, which overlap: the results start at the called function's slot, just
// below the arguments. So each native copies its arguments before writing any
// result, and fills every result slot the caller asked for, with nil past its
// own results, and returns how many results it has: a caller taking all of them
// (`C` = 0) reads up to the stack top, which is set from that count. There are
// only as many result slots as the call's function and arguments take, so a
// native can't return more results than that yet.
//
// Natives are plain functions, with no intern arena and no global table, so the
// strings they make are owned, not interned. `require` finds the built-in
// modules in `MODULES`, registered by `globals` from the values it installs,
// which the global table keeps alive.

thread_local! {
    /// The built-in modules `require` returns, by name, as installed by the
    /// latest `globals`. Their lifetimes are erased; the global table holding
    /// them outlives every call of `require` that can see them.
    static MODULES: RefCell<Vec<(&'static str, LBoxed<'static, 'static>)>> = const { RefCell::new(Vec::new()) };
}

// Note [Native windows]
// ~~~~~~~~~~~~~~~~~~~~~
// A native whose work fits a window op can offer one for a call's arity
// (`NClosure::windowed`), with the type its arguments must have and its
// result's type. A call the specializer knows is to it (a `NativeFunction`
// ctype, which `NativeGuard` checks) guards its arguments to that type (a
// guard the context answers statically, for an argument already known, or a
// discovery thunk, for one of unknown type), and with every argument of that
// type runs as that op, reading its arguments' slots and writing its
// result's slot, the function's, in the register window: no flush and no call.
// The op assumes the arguments' type, unchecked, and the result has its type.
// The native picks the op by which arguments the context knows are in the
// integer encoding (`CType::Integer`, `ints`), which it may read as they are,
// as the bit library's do, whose results are integers too; it reads any other
// number in either encoding.
// Any other call to the native is an ordinary `NativeCall`. The bit library's
// natives offer one for one result from their fixed arities, of numbers,
// computing it as the native does (`bit1`, `bit2`). A call taking every result
// (C = 0) gets exactly the one, and a call taking its arguments up to the top
// (B = 0) has a fixed arity when the specializer knows the top. See Note [Known
// top] in `generator`.

/// A native computing its results from its arguments. See Note [Library natives].
/// With `window:`, also a window op for calls to it, which LBBV runs. See Note
/// [Native windows].
macro_rules! native {
    (window: $window:expr, |$owner:ident, $args:ident| $body:expr) => {{
        let native = match native!(|$owner, $args| $body) {
            LValue::NClosure(n) => LValue::NClosure(NClosure::windowed(n.native(), $window)),
            _ => unreachable!(),
        };
        native
    }};
    (|$owner:ident, $args:ident| $body:expr) => {
        LValue::NClosure(NClosure::new(|mut seq, args, returns, $owner| {
            let $args: SmallVec<[LBoxed<'_, '_>; 8]> = SmallVec::from_slice(args.ro(&seq));
            let results: SmallVec<[LBoxed<'_, '_>; 4]> = $body;
            let _ = &$owner;
            let returns = returns.rw(&mut seq);
            for (i, slot) in returns.iter_mut().enumerate() {
                *slot = results.get(i).copied().unwrap_or(LBoxed::NIL);
            }
            results.len().min(returns.len())
        }))
    };
}

fn arg<'s, 'i>(args: &[LBoxed<'s, 'i>], i: usize) -> LBoxed<'s, 'i> {
    args.get(i).copied().unwrap_or(LBoxed::NIL)
}

fn number(v: LBoxed) -> f64 {
    v.as_number().unwrap_or_else(|| not_a_number(v))
}

/// Out of line: formatting the argument unboxes it, which callers needn't inline.
#[cold]
#[inline(never)]
fn not_a_number(v: LBoxed) -> ! {
    unimplemented!("a number argument, not {:?}", v.unbox())
}

/// An optional number argument.
fn number_or(v: LBoxed, default: f64) -> f64 {
    if v.bits() == LBoxed::NIL.bits() { default } else { number(v) }
}

/// A string or number argument's bytes, as `..` would convert it.
fn bytes(v: LBoxed) -> Vec<u8> {
    match v.unbox() {
        LValue::InternedString(s) => s.as_bytes().to_vec(),
        LValue::OwnedString(s) => s.as_slice().to_vec(),
        LValue::Number(n) => format!("{}", n.0).into_bytes(),
        other => unimplemented!("a string argument, not {other:?}"),
    }
}

fn string<'s, 'i>(bytes: Vec<u8>) -> LBoxed<'s, 'i> {
    LBoxed::box_lvalue(LValue::OwnedString(Gc::string(&bytes)))
}

/// A table argument.
fn table<'s, 'i>(v: LBoxed<'s, 'i>) -> Tc<Table<'s, 'i>> {
    v.as_table().unwrap_or_else(|| unimplemented!("a table argument, not {:?}", v.unbox()))
}

/// Lua's string positions, 1-based and negative from the end, clamped to a
/// string of `len` bytes: the half-open byte range for `i..=j`.
fn span(len: usize, i: f64, j: f64) -> std::ops::Range<usize> {
    let at = |p: f64| if p < 0.0 { len as f64 + p + 1.0 } else { p };
    let (i, j) = (at(i).max(1.0), at(j).min(len as f64));
    if i > j { 0..0 } else { i as usize - 1..j as usize }
}

/// LuaJIT's `bit.tobit`: a number as a 32-bit integer, rounded to nearest (ties
/// to even) and wrapping, as LuaJIT computes it: the low bits of the number
/// plus 2^52 + 2^51.
#[inline(always)]
fn tobit(v: LBoxed) -> i32 {
    to_bit(number(v))
}

#[inline(always)]
fn to_bit(n: f64) -> i32 {
    (n + 6755399441055744.0).to_bits() as u32 as i32
}

/// A number argument of a window op, which the specializer checked. See Note
/// [Native windows].
#[inline(always)]
unsafe fn checked_number(v: LBoxed) -> f64 {
    let Some(n) = v.as_number() else { unsafe { core::hint::unreachable_unchecked() } };
    n
}

fn bit_result<'s, 'i>(x: i32) -> SmallVec<[LBoxed<'s, 'i>; 4]> {
    smallvec![LBoxed::from_int(x)]
}

// The bit operations, by the `OP` of their window ops.
const TOBIT: u8 = 0;
const BNOT: u8 = 1;
const BSWAP: u8 = 2;
const BAND: u8 = 0;
const BOR: u8 = 1;
const BXOR: u8 = 2;
const LSHIFT: u8 = 3;
const RSHIFT: u8 = 4;
const ARSHIFT: u8 = 5;
const ROL: u8 = 6;
const ROR: u8 = 7;

/// A one-operand bit operation.
#[inline(always)]
fn bit1<const OP: u8>(x: i32) -> i32 {
    match OP {
        TOBIT => x,
        BNOT => !x,
        BSWAP => x.swap_bytes(),
        _ => unreachable!(),
    }
}

/// A two-operand bit operation.
#[inline(always)]
fn bit2<const OP: u8>(x: i32, y: i32) -> i32 {
    let n = y as u32 & 31;
    match OP {
        BAND => x & y,
        BOR => x | y,
        BXOR => x ^ y,
        LSHIFT => x.wrapping_shl(n),
        RSHIFT => ((x as u32) >> n) as i32,
        ARSHIFT => x >> n,
        ROL => (x as u32).rotate_left(n) as i32,
        ROR => (x as u32).rotate_right(n) as i32,
        _ => unreachable!(),
    }
}

/// A bit op's window op's argument: in the integer encoding (`INT`), read as it
/// is, or a number of either encoding the specializer checked. See Note
/// [Integers] in `generator`.
#[inline(always)]
unsafe fn bit_arg<const INT: bool>(v: LBoxed) -> i32 {
    if INT { unsafe { v.as_int() } } else { to_bit(unsafe { checked_number(v) }) }
}

// A bit op's result is an i32, so it is in the integer encoding. See Note
// [Integers] in `generator`.
crate::window::windowed!(BitUnary, [], [OP: u8, X: bool], |owner, state, base| (x, out r) {
    *r = LBoxed::from_int(bit1::<OP>(bit_arg::<X>(x)));
});
crate::window::windowed!(BitBinary, [], [OP: u8, X: bool, Y: bool], |owner, state, base| (x, y, out r) {
    *r = LBoxed::from_int(bit2::<OP>(bit_arg::<X>(x), bit_arg::<Y>(y)));
});

/// `bit1::<OP>` as a window op, for a call with one number and one result: its
/// argument in the encoding it has (`ints`).
fn bit1_window<const OP: u8>(a: usize, b: u16, c: u16, ints: &[bool]) -> Option<NativeOp> {
    if !(b == 2 && c == 2) {
        return None;
    }
    let operands = [a + 1, a];
    let window: std::rc::Rc<dyn crate::window::Window> = if ints[0] {
        std::rc::Rc::new(BitUnary::<OP, true>::new(&operands))
    } else {
        std::rc::Rc::new(BitUnary::<OP, false>::new(&operands))
    };
    Some(NativeOp { window, args: LType::Number, result: crate::generator::CType::Integer })
}

/// `bit2::<OP>` as a window op, for a call with two numbers and one result: its
/// arguments in the encodings they have (`ints`).
fn bit2_window<const OP: u8>(a: usize, b: u16, c: u16, ints: &[bool]) -> Option<NativeOp> {
    if !(b == 3 && c == 2) {
        return None;
    }
    let operands = [a + 1, a + 2, a];
    let window: std::rc::Rc<dyn crate::window::Window> = match (ints[0], ints[1]) {
        (false, false) => std::rc::Rc::new(BitBinary::<OP, false, false>::new(&operands)),
        (false, true) => std::rc::Rc::new(BitBinary::<OP, false, true>::new(&operands)),
        (true, false) => std::rc::Rc::new(BitBinary::<OP, true, false>::new(&operands)),
        (true, true) => std::rc::Rc::new(BitBinary::<OP, true, true>::new(&operands)),
    };
    Some(NativeOp { window, args: LType::Number, result: crate::generator::CType::Integer })
}

/// A table of `entries`, keyed by interned names.
fn module<'s, 'i>(intern: &'i internment::Arena<IStr<'s>>, entries: Vec<(&str, LValue<'s, 'i>)>) -> LValue<'s, 'i> {
    let mut t = Table::new(0, entries.len());
    for (name, value) in entries {
        t.insert_lvalue(InternString::intern(intern, name), value);
    }
    LValue::Table(Tc::new(t))
}

/// The library's globals, by name, to install in the global table.
pub fn globals<'s, 'i>(intern: &'i internment::Arena<IStr<'s>>) -> Vec<(LValue<'s, 'i>, LValue<'s, 'i>)> {
    let type_ = native!(|owner, args| {
        let name: &[u8] = match arg(&args, 0).unbox() {
            LValue::Nil => b"nil",
            LValue::Bool(_) => b"boolean",
            LValue::Number(_) => b"number",
            LValue::InternedString(_) | LValue::OwnedString(_) => b"string",
            LValue::Table(_) => b"table",
            LValue::LClosure(_) | LValue::NClosure(_) => b"function",
        };
        smallvec![string(name.to_vec())]
    });
    let tostring = native!(|owner, args| {
        let s = arg(&args, 0).unbox().as_string(owner).expect("a string form");
        smallvec![LBoxed::box_lvalue(LValue::OwnedString(s))]
    });
    let tonumber = native!(|owner, args| {
        let v = arg(&args, 0);
        let base = number_or(arg(&args, 1), 10.0) as u32;
        let parsed = match v.unbox() {
            LValue::Number(_) if base == 10 => v.as_number(),
            LValue::InternedString(_) | LValue::OwnedString(_) => {
                let text = String::from_utf8_lossy(&bytes(v)).trim().to_lowercase();
                match text.strip_prefix("0x") {
                    Some(hex) if base == 10 || base == 16 => i64::from_str_radix(hex, 16).ok().map(|n| n as f64),
                    _ if base == 10 => text.parse::<f64>().ok().filter(|n| n.is_finite() || text.contains("inf")),
                    _ => i64::from_str_radix(&text, base).ok().map(|n| n as f64),
                }
            }
            _ => None,
        };
        smallvec![parsed.map_or(LBoxed::NIL, LBoxed::from_number)]
    });

    let string_lib = module(intern, vec![
        ("len", native!(|owner, args| smallvec![LBoxed::from_number(bytes(arg(&args, 0)).len() as f64)])),
        ("sub", native!(|owner, args| {
            let s = bytes(arg(&args, 0));
            let range = span(s.len(), number_or(arg(&args, 1), 1.0), number_or(arg(&args, 2), -1.0));
            smallvec![string(s[range].to_vec())]
        })),
        ("byte", native!(|owner, args| {
            let s = bytes(arg(&args, 0));
            let i = number_or(arg(&args, 1), 1.0);
            let range = span(s.len(), i, number_or(arg(&args, 2), i));
            s[range].iter().map(|&b| LBoxed::from_number(b as f64)).collect()
        })),
        ("char", native!(|owner, args| smallvec![string(args.iter().map(|&b| number(b) as u8).collect())])),
    ]);

    let table_new = native!(|owner, args| {
        let t = Table {
            array: FVec::from(Vec::with_capacity(number_or(arg(&args, 0), 0.0) as usize)),
            hash: IndexMap::with_capacity_and_hasher(number_or(arg(&args, 1), 0.0) as usize, InternedHasher::default()),
            epoch: 0,
            environment: false,
        };
        smallvec![LBoxed::box_lvalue(LValue::Table(Tc::new(t)))]
    });
    let table_clear = native!(|owner, args| {
        let t = table(arg(&args, 0));
        let t = t.rw(owner);
        t.array.clear();
        t.clear_hash();
        t.epoch += 1;
        smallvec![]
    });
    let table_lib = module(intern, vec![
        ("new", table_new.clone()),
        ("clear", table_clear.clone()),
        ("insert", native!(|owner, args| {
            let t = table(arg(&args, 0));
            t.barrier_back();
            let array = &mut t.rw(owner).array;
            match args.len() {
                2 => array.push(arg(&args, 1)),
                _ => {
                    let at = (number(arg(&args, 1)) as usize).clamp(1, array.len() + 1) - 1;
                    array.insert(at, arg(&args, 2));
                }
            }
            smallvec![]
        })),
        ("concat", native!(|owner, args| {
            let t = table(arg(&args, 0));
            let sep = if args.len() > 1 { bytes(arg(&args, 1)) } else { Vec::new() };
            let items: Vec<LBoxed> = t.ro(owner).array.iter().copied().collect();
            let range = span(items.len(), number_or(arg(&args, 2), 1.0), number_or(arg(&args, 3), items.len() as f64));
            let mut out = Vec::new();
            for (n, &item) in items[range].iter().enumerate() {
                if n > 0 {
                    out.extend_from_slice(&sep);
                }
                out.extend_from_slice(&bytes(item));
            }
            smallvec![string(out)]
        })),
    ]);

    let io_lib = module(intern, vec![
        ("write", native!(|owner, args| {
            let mut out = std::io::stdout().lock();
            for &v in &args {
                out.write_all(&bytes(v)).expect("writing stdout");
            }
            smallvec![]
        })),
        // The benchmarks' `io.write` that discards its output.
        ("write_devnull", native!(|owner, args| smallvec![])),
    ]);

    let bit_lib = module(intern, vec![
        ("tobit", native!(window: bit1_window::<TOBIT>, |owner, args| bit_result(bit1::<TOBIT>(tobit(arg(&args, 0)))))),
        ("bnot", native!(window: bit1_window::<BNOT>, |owner, args| bit_result(bit1::<BNOT>(tobit(arg(&args, 0)))))),
        ("band", native!(window: bit2_window::<BAND>, |owner, args| bit_result(args.iter().fold(-1, |x, &v| bit2::<BAND>(x, tobit(v)))))),
        ("bor", native!(window: bit2_window::<BOR>, |owner, args| bit_result(args.iter().fold(0, |x, &v| bit2::<BOR>(x, tobit(v)))))),
        ("bxor", native!(window: bit2_window::<BXOR>, |owner, args| bit_result(args.iter().fold(0, |x, &v| bit2::<BXOR>(x, tobit(v)))))),
        ("lshift", native!(window: bit2_window::<LSHIFT>, |owner, args| bit_result(bit2::<LSHIFT>(tobit(arg(&args, 0)), tobit(arg(&args, 1)))))),
        ("rshift", native!(window: bit2_window::<RSHIFT>, |owner, args| bit_result(bit2::<RSHIFT>(tobit(arg(&args, 0)), tobit(arg(&args, 1)))))),
        ("arshift", native!(window: bit2_window::<ARSHIFT>, |owner, args| bit_result(bit2::<ARSHIFT>(tobit(arg(&args, 0)), tobit(arg(&args, 1)))))),
        ("rol", native!(window: bit2_window::<ROL>, |owner, args| bit_result(bit2::<ROL>(tobit(arg(&args, 0)), tobit(arg(&args, 1)))))),
        ("ror", native!(window: bit2_window::<ROR>, |owner, args| bit_result(bit2::<ROR>(tobit(arg(&args, 0)), tobit(arg(&args, 1)))))),
        ("bswap", native!(window: bit1_window::<BSWAP>, |owner, args| bit_result(bit1::<BSWAP>(tobit(arg(&args, 0)))))),
    ]);

    let require = native!(|owner, args| {
        let name = bytes(arg(&args, 0));
        let found = MODULES.with_borrow(|modules| modules.iter().find(|(m, _)| m.as_bytes() == name).map(|(_, v)| *v));
        let Some(module) = found else { panic!("require: no built-in module {:?}", String::from_utf8_lossy(&name)) };
        // SAFETY: the value is alive, held by the global table; see `MODULES`.
        smallvec![unsafe { std::mem::transmute::<LBoxed<'static, 'static>, LBoxed<'_, '_>>(module) }]
    });

    let erase = |v: &LValue<'s, 'i>| {
        let boxed = LBoxed::box_lvalue(v.clone());
        // SAFETY: only the lifetimes change; see `MODULES`.
        unsafe { std::mem::transmute::<LBoxed<'s, 'i>, LBoxed<'static, 'static>>(boxed) }
    };
    MODULES.with_borrow_mut(|modules| {
        *modules = vec![("bit", erase(&bit_lib)), ("table.new", erase(&table_new)), ("table.clear", erase(&table_clear))];
    });

    vec![
        (InternString::intern(intern, "type"), type_),
        (InternString::intern(intern, "tostring"), tostring),
        (InternString::intern(intern, "tonumber"), tonumber),
        (InternString::intern(intern, "require"), require),
        (InternString::intern(intern, "string"), string_lib),
        (InternString::intern(intern, "table"), table_lib),
        (InternString::intern(intern, "io"), io_lib),
        (InternString::intern(intern, "bit"), bit_lib),
    ]
}
