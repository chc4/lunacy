//! The parts of Lua's standard library (and LuaJIT's `bit`, `table.new` and
//! `table.clear` extensions) that lunacy has, as natives in the global table.
//! See Note [Library natives].

use std::cell::RefCell;
use std::io::Write;

use indexmap::IndexMap;
use smallvec::{smallvec, SmallVec};

use crate::gc::Gc;
use crate::lboxed::LBoxed;
use crate::vm::{FVec, IStr, InternString, InternedHasher, LValue, NClosure, Table, Tc};

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

/// A native computing its results from its arguments. See Note [Library natives].
macro_rules! native {
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
    v.as_number().unwrap_or_else(|| unimplemented!("a number argument, not {:?}", v.unbox()))
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
    LBoxed::box_lvalue(LValue::OwnedString(Gc::new(FVec::from(bytes))))
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

/// LuaJIT's `bit.tobit`: a number as a 32-bit integer, wrapping.
fn tobit(v: LBoxed) -> i32 {
    number(v) as i64 as i32
}

fn bit_result<'s, 'i>(x: i32) -> SmallVec<[LBoxed<'s, 'i>; 4]> {
    smallvec![LBoxed::from_number(x as f64)]
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
        };
        smallvec![LBoxed::box_lvalue(LValue::Table(Tc::new(t)))]
    });
    let table_clear = native!(|owner, args| {
        let t = table(arg(&args, 0));
        let t = t.rw(owner);
        t.array.clear();
        t.hash.clear();
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
        ("tobit", native!(|owner, args| bit_result(tobit(arg(&args, 0))))),
        ("bnot", native!(|owner, args| bit_result(!tobit(arg(&args, 0))))),
        ("band", native!(|owner, args| bit_result(args.iter().fold(-1, |x, &v| x & tobit(v))))),
        ("bor", native!(|owner, args| bit_result(args.iter().fold(0, |x, &v| x | tobit(v))))),
        ("bxor", native!(|owner, args| bit_result(args.iter().fold(0, |x, &v| x ^ tobit(v))))),
        ("lshift", native!(|owner, args| bit_result(tobit(arg(&args, 0)).wrapping_shl(tobit(arg(&args, 1)) as u32 & 31)))),
        ("rshift", native!(|owner, args| bit_result(((tobit(arg(&args, 0)) as u32) >> (tobit(arg(&args, 1)) as u32 & 31)) as i32))),
        ("arshift", native!(|owner, args| bit_result(tobit(arg(&args, 0)) >> (tobit(arg(&args, 1)) as u32 & 31)))),
        ("rol", native!(|owner, args| bit_result((tobit(arg(&args, 0)) as u32).rotate_left(tobit(arg(&args, 1)) as u32 & 31) as i32))),
        ("ror", native!(|owner, args| bit_result((tobit(arg(&args, 0)) as u32).rotate_right(tobit(arg(&args, 1)) as u32 & 31) as i32))),
        ("bswap", native!(|owner, args| bit_result(tobit(arg(&args, 0)).swap_bytes()))),
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
