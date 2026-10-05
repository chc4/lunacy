//! The parts of Lua's standard library (and LuaJIT's `bit`, `table.new` and
//! `table.clear` extensions) that lunacy has, as natives in the global table.
//! See Note [Library natives].

use std::cell::{Cell, RefCell};
use std::io::Write;

use indexmap::IndexMap;
use smallvec::{smallvec, SmallVec};

use crate::gc::Gc;
use crate::lboxed::LBoxed;
use crate::vm::{FVec, IStr, InternString, InternedHasher, LType, LValue, NClosure, Table, Tc, Userdata};
use crate::vm::NativeOp;
use crate::patterns::{self, Capture};

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
// A native given the owner mutable can write any object the program can see,
// in ways the specializer can't model, so a call to one is assumed to have done
// anything. A pure native is given the owner shared: it can read any object, and
// make new ones, but write none the program could already see, so a call to one
// has no effects the specializer tracks.
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
// integer encoding (`CType::Type(LType::Integer)`, `ints`), which it may read as they are,
// as the bit library's do, whose results are integers too; it reads any other
// number in either encoding.
// Any other call to the native is an ordinary `NativeCall`. The bit library's
// natives offer one for one result from their fixed arities, of numbers,
// computing it as the native does (`bit1`, `bit2`). A call taking every result
// (C = 0) gets exactly the one, and a call taking its arguments up to the top
// (B = 0) has a fixed arity when the specializer knows the top. See Note [Known
// top] in `specialize`.

/// Raise `message` as an error, which ends the program.
fn raise(message: String) -> ! {
    panic!("error: {message}")
}

/// `type`'s name for a value's type.
fn type_name(v: LBoxed) -> &'static [u8] {
    match v.unbox() {
        LValue::Nil => b"nil",
        LValue::Bool(_) => b"boolean",
        LValue::Integer(_) | LValue::Double(_) => b"number",
        LValue::InternedString(_) | LValue::OwnedString(_) => b"string",
        LValue::Table(_) => b"table",
        LValue::LClosure(_) | LValue::NClosure(_) => b"function",
        LValue::Userdata(_) => b"userdata",
    }
}

/// A capture of a match in `src`: its bytes, or its position. See Note
/// [Patterns] in `patterns`.
fn capture<'s, 'i>(src: &[u8], capture: Capture) -> LBoxed<'s, 'i> {
    match capture {
        Capture::Bytes(range) => string(src[range].to_vec()),
        Capture::Position(at) => LBoxed::from_int(at as i32),
    }
}

/// Where `string.find` and `string.match` start, from their `init`
/// argument: 1-based and negative from the end, clamped to the string.
fn init(len: usize, v: LBoxed) -> usize {
    let init = number_or(v, 1.0) as i64;
    let init = if init < 0 { init + len as i64 + 1 } else { init };
    (init - 1).clamp(0, len as i64) as usize
}

/// `string.gsub`'s replacement string for a match: `%0` to `%9` its captures,
/// `%` and anything else that byte.
fn substitute(src: &[u8], replacement: &[u8], found: &patterns::Found) -> Result<Vec<u8>, String> {
    let mut out = vec![];
    let mut bytes = replacement.iter();
    while let Some(&b) = bytes.next() {
        if b != b'%' {
            out.push(b);
            continue;
        }
        match bytes.next().copied().unwrap_or(0) {
            b'0' => out.extend_from_slice(&src[found.range.clone()]),
            d @ b'1'..=b'9' => match found.capture((d - b'1') as usize)? {
                Capture::Bytes(range) => out.extend_from_slice(&src[range]),
                Capture::Position(at) => out.extend_from_slice(at.to_string().as_bytes()),
            },
            other => out.push(other),
        }
    }
    Ok(out)
}

/// A native computing its results from its arguments. See Note [Library natives].
/// With `pure`, given the owner shared, so it writes no object the program can
/// see; with `window:`, also a window op for calls to it, which LBBV runs. See
/// Note [Native windows].
macro_rules! native {
    (pure window: $window:expr, |$owner:ident, $args:ident| $body:expr) => {
        LValue::NClosure(NClosure::pure_windowed(native!(@fn $owner, $args, $body), $window))
    };
    (pure |$owner:ident, $args:ident| $body:expr) => {
        LValue::NClosure(NClosure::pure(native!(@fn $owner, $args, $body)))
    };
    (|$owner:ident, $args:ident| $body:expr) => {
        LValue::NClosure(NClosure::new(native!(@fn $owner, $args, $body)))
    };
    (@fn $owner:ident, $args:ident, $body:expr) => {
        |mut seq, args, returns, $owner| {
            let $args: SmallVec<[LBoxed<'_, '_>; 8]> = SmallVec::from_slice(args.ro(&seq));
            let results: SmallVec<[LBoxed<'_, '_>; 4]> = $body;
            let _ = &$owner;
            let returns = returns.rw(&mut seq);
            for (slot, &result) in returns.iter_mut().zip(results.iter()) {
                *slot = result;
            }
            results.len().min(returns.len())
        }
    };
}

thread_local! {
    /// `math.random`'s state: xorshift64, which `math.randomseed` reseeds.
    static RANDOM: Cell<u64> = const { Cell::new(0x2545_f491_4f6c_dd1d) };
}

/// The next number `math.random` draws on, in [0, 1).
fn random() -> f64 {
    RANDOM.with(|state| {
        let mut x = state.get();
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        state.set(x);
        (x >> 11) as f64 / (1u64 << 53) as f64
    })
}

/// One conversion of `string.format` through C's `snprintf`, as Lua's is:
/// `spec` its flags, width and precision, `conv` the conversion with any
/// length modifier.
fn c_format(spec: &[u8], conv: &str, value: CArg) -> Vec<u8> {
    let format = std::ffi::CString::new([b"%", spec, conv.as_bytes()].concat()).expect("a format without NUL");
    let mut buf = vec![0u8; 64];
    loop {
        // SAFETY: `format` has the one conversion `value` is the argument of.
        let n = unsafe {
            match value {
                CArg::Int(v) => libc::snprintf(buf.as_mut_ptr().cast(), buf.len(), format.as_ptr(), v as libc::c_longlong),
                CArg::Char(v) => libc::snprintf(buf.as_mut_ptr().cast(), buf.len(), format.as_ptr(), v as libc::c_int),
                CArg::Double(v) => libc::snprintf(buf.as_mut_ptr().cast(), buf.len(), format.as_ptr(), v as libc::c_double),
            }
        } as usize;
        if n < buf.len() {
            buf.truncate(n);
            return buf;
        }
        buf.resize(n + 1, 0);
    }
}

#[derive(Clone, Copy)]
enum CArg {
    Int(i64),
    Char(i32),
    Double(f64),
}

/// `string.format(fmt, ...)`.
fn format(fmt: &[u8], args: &[LBoxed]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut next = 0;
    let mut i = 0;
    while i < fmt.len() {
        if fmt[i] != b'%' {
            out.push(fmt[i]);
            i += 1;
            continue;
        }
        i += 1;
        if fmt.get(i) == Some(&b'%') {
            out.push(b'%');
            i += 1;
            continue;
        }
        let start = i;
        while i < fmt.len() && b"-+ #0".contains(&fmt[i]) {
            i += 1;
        }
        while i < fmt.len() && (fmt[i].is_ascii_digit() || fmt[i] == b'.') {
            i += 1;
        }
        let spec = &fmt[start..i];
        let conv = *fmt.get(i).unwrap_or_else(|| panic!("string.format: a format ending in its conversion's spec"));
        i += 1;
        let value = arg(args, next);
        next += 1;
        match conv {
            b'd' | b'i' => out.extend(c_format(spec, "lld", CArg::Int(number(value) as i64))),
            b'u' | b'o' | b'x' | b'X' => out.extend(c_format(spec, &format!("ll{}", conv as char), CArg::Int(number(value) as i64))),
            b'c' => out.extend(c_format(spec, "c", CArg::Char(number(value) as i32))),
            b'e' | b'E' | b'f' | b'g' | b'G' => out.extend(c_format(spec, &(conv as char).to_string(), CArg::Double(number(value)))),
            b's' => {
                let mut s = bytes(value);
                let text = String::from_utf8_lossy(spec).into_owned();
                let (width, precision) = match text.split_once('.') {
                    Some((w, p)) => (w, p.parse::<usize>().ok()),
                    None => (text.as_str(), None),
                };
                if let Some(p) = precision {
                    s.truncate(p);
                }
                let left = width.contains('-');
                let width: usize = width.trim_start_matches(|c: char| !c.is_ascii_digit()).parse().unwrap_or(0);
                let pad = width.saturating_sub(s.len());
                if !left {
                    out.extend(std::iter::repeat_n(b' ', pad));
                }
                out.extend(s);
                if left {
                    out.extend(std::iter::repeat_n(b' ', pad));
                }
            }
            b'q' => {
                out.push(b'"');
                for b in bytes(value) {
                    match b {
                        b'"' | b'\\' | b'\n' => out.extend([b'\\', b]),
                        b'\r' => out.extend(b"\\r"),
                        0 => out.extend(b"\\000"),
                        b => out.push(b),
                    }
                }
                out.push(b'"');
            }
            conv => panic!("string.format: no conversion '%{}'", conv as char),
        }
    }
    out
}

/// `math`'s natives beside those `Vm::global_env` defines.
pub fn math_natives<'s, 'i>() -> Vec<(&'static str, LValue<'s, 'i>)> {
    macro_rules! math1 {
        ($op:ident) => {
            native!(pure window: math1_window::<$op>, |owner, args| smallvec![math1_boxed::<$op>(number(arg(&args, 0)))])
        };
    }
    vec![
        ("floor", math1!(FLOOR)),
        ("ceil", math1!(CEIL)),
        ("sqrt", math1!(SQRT)),
        ("abs", math1!(ABS)),
        ("sin", math1!(SIN)),
        ("cos", math1!(COS)),
        ("tan", math1!(TAN)),
        ("random", native!(pure |owner, args| {
            let r = random();
            // A whole number from a range, in the integer encoding where an i32
            // holds it: the code using it computes on an integer. See Note
            // [Narrowing] in `specialize`.
            smallvec![match args.len() {
                0 => LBoxed::from_double(r),
                1 => LBoxed::from_number((r * number(args[0]).floor()).floor() + 1.0),
                _ => {
                    let (m, n) = (number(args[0]).floor(), number(args[1]).floor());
                    LBoxed::from_number(m + (r * (n - m + 1.0)).floor())
                }
            }]
        })),
        ("randomseed", native!(pure |owner, args| {
            // Never zero, which xorshift stays at.
            RANDOM.with(|state| state.set(number(arg(&args, 0)).to_bits() ^ 0x9e37_79b9_7f4a_7c15 | 1));
            smallvec![]
        })),
        ("max", native!(pure |owner, args| smallvec![LBoxed::from_double(args.iter().map(|&v| number(v)).fold(f64::NEG_INFINITY, f64::max))])),
        ("min", native!(pure |owner, args| smallvec![LBoxed::from_double(args.iter().map(|&v| number(v)).fold(f64::INFINITY, f64::min))])),
    ]
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
        LValue::Integer(i) => format!("{}", i).into_bytes(),
        LValue::Double(n) => format!("{}", n.0).into_bytes(),
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

const FLOOR: u8 = 0;
const CEIL: u8 = 1;
const SQRT: u8 = 2;
const ABS: u8 = 3;
const SIN: u8 = 4;
const COS: u8 = 5;
const TAN: u8 = 6;

/// A one-number function of the math library.
#[inline(always)]
fn math1<const OP: u8>(x: f64) -> f64 {
    match OP {
        FLOOR => x.floor(),
        CEIL => x.ceil(),
        SQRT => x.sqrt(),
        ABS => x.abs(),
        SIN => x.sin(),
        COS => x.cos(),
        TAN => x.tan(),
        _ => unreachable!(),
    }
}

/// `math1::<OP>`'s result, a double like every number a native computes. See
/// Note [Integers] in `specialize`.
#[inline(always)]
fn math1_boxed<'s, 'i, const OP: u8>(x: f64) -> LBoxed<'s, 'i> {
    LBoxed::from_double(math1::<OP>(x))
}

crate::window::windowed!(MathUnary, [], [OP: u8, X: bool], |owner, state, base| (x, out r) {
    let x = if X { (unsafe { x.as_int() }) as f64 } else { unsafe { checked_number(x) } };
    *r = math1_boxed::<OP>(x);
});

/// `math1::<OP>` as a window op, for a call with one number and one result: its
/// argument in the encoding it has (`ints`).
fn math1_window<const OP: u8>(a: usize, b: u16, c: u16, ints: &[bool]) -> Option<NativeOp> {
    if !(b == 2 && c == 2) {
        return None;
    }
    let operands = [a + 1, a];
    let window: std::rc::Rc<dyn crate::window::Window> = if ints[0] {
        std::rc::Rc::new(MathUnary::<OP, true>::new(&operands))
    } else {
        std::rc::Rc::new(MathUnary::<OP, false>::new(&operands))
    };
    let result = crate::specialize::CType::Type(LType::Double);
    Some(NativeOp { window, args: crate::specialize::CType::Number, result })
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
/// [Integers] in `specialize`.
#[inline(always)]
unsafe fn bit_arg<const INT: bool>(v: LBoxed) -> i32 {
    if INT { unsafe { v.as_int() } } else { to_bit(unsafe { checked_number(v) }) }
}

// A bit op's result is an i32, so it is in the integer encoding. See Note
// [Integers] in `specialize`.
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
    Some(NativeOp { window, args: crate::specialize::CType::Number, result: crate::specialize::CType::Type(LType::Integer) })
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
    Some(NativeOp { window, args: crate::specialize::CType::Number, result: crate::specialize::CType::Type(LType::Integer) })
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
    let type_ = native!(pure |owner, args| smallvec![string(type_name(arg(&args, 0)).to_vec())]);
    let tostring = native!(pure |owner, args| {
        let s = arg(&args, 0).unbox().as_string(owner).expect("a string form");
        smallvec![LBoxed::box_lvalue(LValue::OwnedString(s))]
    });
    let tonumber = native!(pure |owner, args| {
        let v = arg(&args, 0);
        let base = number_or(arg(&args, 1), 10.0) as u32;
        let parsed = match v.unbox() {
            LValue::Integer(_) | LValue::Double(_) if base == 10 => v.as_number(),
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
        smallvec![parsed.map_or(LBoxed::NIL, LBoxed::from_double)]
    });

    let string_lib = module(intern, vec![
        ("len", native!(pure |owner, args| smallvec![LBoxed::from_int(bytes(arg(&args, 0)).len() as i32)])),
        ("sub", native!(pure |owner, args| {
            let s = bytes(arg(&args, 0));
            let range = span(s.len(), number_or(arg(&args, 1), 1.0), number_or(arg(&args, 2), -1.0));
            smallvec![string(s[range].to_vec())]
        })),
        ("byte", native!(pure |owner, args| {
            let s = bytes(arg(&args, 0));
            let i = number_or(arg(&args, 1), 1.0);
            let range = span(s.len(), i, number_or(arg(&args, 2), i));
            s[range].iter().map(|&b| LBoxed::from_int(b as i32)).collect()
        })),
        ("char", native!(pure |owner, args| smallvec![string(args.iter().map(|&b| number(b) as u8).collect())])),
        ("rep", native!(pure |owner, args| {
            let s = bytes(arg(&args, 0));
            let n = number(arg(&args, 1)).max(0.0) as usize;
            let out = s.repeat(n);
            smallvec![string(out)]
        })),
        ("format", native!(pure |owner, args| smallvec![string(format(&bytes(arg(&args, 0)), args.get(1..).unwrap_or(&[])))])),
        // See Note [Patterns] in `patterns`.
        ("find", native!(pure |owner, args| {
            let (s, p) = (bytes(arg(&args, 0)), bytes(arg(&args, 1)));
            let init = init(s.len(), arg(&args, 2));
            if arg(&args, 3).truthy() || !patterns::has_specials(&p) {
                match patterns::find_plain(&s[init..], &p) {
                    Some(at) => smallvec![LBoxed::from_int((init + at + 1) as i32), LBoxed::from_int((init + at + p.len()) as i32)],
                    None => smallvec![LBoxed::NIL],
                }
            } else {
                let found = patterns::find(&s, &p, init, |found| {
                    let mut results: SmallVec<[LBoxed<'_, '_>; 4]> = smallvec![LBoxed::from_int(found.range.start as i32 + 1), LBoxed::from_int(found.range.end as i32)];
                    results.extend(found.explicit()?.into_iter().map(|c| capture(&s, c)));
                    Ok(results)
                });
                found.unwrap_or_else(|message| raise(message)).unwrap_or_else(|| smallvec![LBoxed::NIL])
            }
        })),
        ("match", native!(pure |owner, args| {
            let (s, p) = (bytes(arg(&args, 0)), bytes(arg(&args, 1)));
            let found = patterns::find(&s, &p, init(s.len(), arg(&args, 2)), |found| {
                Ok(found.captures()?.into_iter().map(|c| capture(&s, c)).collect())
            });
            found.unwrap_or_else(|message| raise(message)).unwrap_or_else(|| smallvec![LBoxed::NIL])
        })),
        ("gsub", native!(pure |owner, args| {
            let (s, p, replacement) = (bytes(arg(&args, 0)), bytes(arg(&args, 1)), arg(&args, 2));
            let max = if arg(&args, 3).bits() == LBoxed::NIL.bits() { s.len() as i64 + 1 } else { number(arg(&args, 3)) as i64 };
            let replaced = match replacement.unbox() {
                LValue::Integer(_) | LValue::Double(_) | LValue::InternedString(_) | LValue::OwnedString(_) => {
                    let replacement = bytes(replacement);
                    patterns::gsub(&s, &p, max, |found| substitute(&s, &replacement, found).map(Some))
                },
                // The value at the first capture, raw, if it's a string or a number;
                // a false one keeps the match.
                LValue::Table(t) => patterns::gsub(&s, &p, max, |found| {
                    let value = match found.capture(0)? {
                        Capture::Bytes(range) => t.get_string(owner, &s[range]),
                        Capture::Position(at) => t.get_number(owner, at as f64),
                    };
                    match value.unbox() {
                        LValue::Nil | LValue::Bool(false) => Ok(None),
                        LValue::Integer(_) | LValue::Double(_) | LValue::InternedString(_) | LValue::OwnedString(_) => Ok(Some(bytes(value))),
                        _ => Err(format!("invalid replacement value (a {})", String::from_utf8_lossy(type_name(value)))),
                    }
                }),
                LValue::LClosure(_) | LValue::NClosure(_) => unimplemented!("string.gsub with a function replacement: a native can't call a function"),
                _ => raise("bad argument #3 to 'gsub' (string/function/table expected)".into()),
            };
            let (out, n) = replaced.unwrap_or_else(|message| raise(message));
            smallvec![string(out), LBoxed::from_int(n as i32)]
        })),
    ]);

    let table_new = native!(pure |owner, args| {
        let t = Table {
            array: FVec::from(Vec::with_capacity(number_or(arg(&args, 0), 0.0) as usize)),
            hash: IndexMap::with_capacity_and_hasher(number_or(arg(&args, 1), 0.0) as usize, InternedHasher::default()),
            epoch: 0,
            environment: false,
            kind: 0,
        };
        smallvec![LBoxed::box_lvalue(LValue::Table(Tc::new(t)))]
    });
    let table_clear = native!(|owner, args| {
        let t = table(arg(&args, 0));
        let t = t.rw(owner);
        t.array.clear();
        t.kind = 0;
        t.clear_hash();
        t.epoch += 1;
        smallvec![]
    });
    let table_lib = module(intern, vec![
        ("new", table_new.clone()),
        ("clear", table_clear.clone()),
        // Lua 5.1's `tinsert`: the value goes at the position, or at the end
        // (`#t + 1`) without one. A position from 1 to the end moves the
        // elements from it up one; one past the end moves nothing; one below 1
        // moves every element up one, down to the position.
        ("insert", native!(|owner, args| {
            let mut t = table(arg(&args, 0));
            let value = arg(&args, args.len() - 1);
            let end = t.ro(owner).array.len() as i64 + 1;
            let pos = if args.len() == 2 { end } else { number(arg(&args, 1)) as i64 };
            if (1..=end).contains(&pos) {
                t.barrier_back();
                let tab = t.rw(owner);
                tab.array.insert(pos as usize - 1, value);
                tab.widen_kind(value.representation());
                // See Note [Array length].
                tab.trim();
            } else {
                for i in (pos + 1..=end.max(pos)).rev() {
                    let moved = t.get_number(owner, (i - 1) as f64);
                    t.set_number(owner, i as f64, moved);
                }
                t.set_number(owner, pos as f64, value);
            }
            smallvec![]
        })),
        ("remove", native!(|owner, args| {
            let t = table(arg(&args, 0));
            let tab = t.rw(owner);
            let at = if args.len() > 1 { number(arg(&args, 1)) as usize } else { tab.array.len() };
            if (1..=tab.array.len()).contains(&at) {
                let removed = tab.array.remove(at - 1);
                // See Note [Array length].
                tab.trim();
                smallvec![removed]
            } else {
                smallvec![]
            }
        })),
        ("concat", native!(pure |owner, args| {
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
        ("write", native!(pure |owner, args| {
            let mut out = std::io::stdout().lock();
            for &v in &args {
                out.write_all(&bytes(v)).expect("writing stdout");
            }
            smallvec![]
        })),
        // The benchmarks' `io.write` that discards its output.
        ("write_devnull", native!(pure |owner, args| smallvec![])),
    ]);

    let bit_lib = module(intern, vec![
        ("tobit", native!(pure window: bit1_window::<TOBIT>, |owner, args| bit_result(bit1::<TOBIT>(tobit(arg(&args, 0)))))),
        ("bnot", native!(pure window: bit1_window::<BNOT>, |owner, args| bit_result(bit1::<BNOT>(tobit(arg(&args, 0)))))),
        ("band", native!(pure window: bit2_window::<BAND>, |owner, args| bit_result(args.iter().fold(-1, |x, &v| bit2::<BAND>(x, tobit(v)))))),
        ("bor", native!(pure window: bit2_window::<BOR>, |owner, args| bit_result(args.iter().fold(0, |x, &v| bit2::<BOR>(x, tobit(v)))))),
        ("bxor", native!(pure window: bit2_window::<BXOR>, |owner, args| bit_result(args.iter().fold(0, |x, &v| bit2::<BXOR>(x, tobit(v)))))),
        ("lshift", native!(pure window: bit2_window::<LSHIFT>, |owner, args| bit_result(bit2::<LSHIFT>(tobit(arg(&args, 0)), tobit(arg(&args, 1)))))),
        ("rshift", native!(pure window: bit2_window::<RSHIFT>, |owner, args| bit_result(bit2::<RSHIFT>(tobit(arg(&args, 0)), tobit(arg(&args, 1)))))),
        ("arshift", native!(pure window: bit2_window::<ARSHIFT>, |owner, args| bit_result(bit2::<ARSHIFT>(tobit(arg(&args, 0)), tobit(arg(&args, 1)))))),
        ("rol", native!(pure window: bit2_window::<ROL>, |owner, args| bit_result(bit2::<ROL>(tobit(arg(&args, 0)), tobit(arg(&args, 1)))))),
        ("ror", native!(pure window: bit2_window::<ROR>, |owner, args| bit_result(bit2::<ROR>(tobit(arg(&args, 0)), tobit(arg(&args, 1)))))),
        ("bswap", native!(pure window: bit1_window::<BSWAP>, |owner, args| bit_result(bit1::<BSWAP>(tobit(arg(&args, 0)))))),
    ]);

    // Every value of `t` from `i` to `j`, by default all of its array part.
    let unpack = native!(pure |owner, args| {
        let t = table(arg(&args, 0));
        let array = &t.ro(owner).array;
        let i = number_or(arg(&args, 1), 1.0) as i64;
        let j = number_or(arg(&args, 2), array.len() as f64) as i64;
        (i..=j).map(|k| if k >= 1 { array.get(k as usize - 1).copied().unwrap_or(LBoxed::NIL) } else { LBoxed::NIL }).collect()
    });
    // Lua 5.1's `newproxy`: a new userdata with no metatable, with a new empty
    // one (`true`), or sharing a userdata's, which it must have.
    let newproxy = native!(pure |owner, args| {
        let metatable = match arg(&args, 0).unbox() {
            LValue::Nil | LValue::Bool(false) => Ok(None),
            LValue::Bool(true) => Ok(Some(Tc::new(Table::new(0, 0)))),
            LValue::Userdata(proxy) => proxy.ro(owner).metatable().cloned().map(Some).ok_or(()),
            _ => Err(()),
        };
        match metatable {
            Ok(metatable) => smallvec![LBoxed::box_lvalue(LValue::Userdata(Tc::new(Userdata::new(metatable))))],
            Err(()) => raise("bad argument #1 to 'newproxy' (boolean or proxy expected)".into()),
        }
    });
    // Lunacy has no `pcall`: an error ends the run.
    let error = native!(pure |owner, args| {
        let message = arg(&args, 0).unbox().as_string(owner).map(|s| String::from_utf8_lossy(s.as_slice()).into_owned());
        raise(message.unwrap_or_else(|| format!("{:?}", arg(&args, 0).unbox())))
    });

    let require = native!(pure |owner, args| {
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
        (InternString::intern(intern, "unpack"), unpack),
        (InternString::intern(intern, "error"), error),
        (InternString::intern(intern, "newproxy"), newproxy),
        (InternString::intern(intern, "string"), string_lib),
        (InternString::intern(intern, "table"), table_lib),
        (InternString::intern(intern, "io"), io_lib),
        (InternString::intern(intern, "bit"), bit_lib),
    ]
}
