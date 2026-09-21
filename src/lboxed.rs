//! The NuN-boxed value type, `LBoxed`, in a module of its own so its `u64`
//! payload can be a *private* field. That seal is what makes `unbox` safe: the
//! only ways to obtain an `LBoxed` are the safe constructors here (`box_lvalue`,
//! `from_number`, `from_bool`, `interned`, `NIL`, `From<&LConstant>`), each of
//! which produces bits that validly encode a live value. Since no code outside
//! this module can fabricate an `LBoxed` from arbitrary bits, decoding one is no
//! less safe than dereferencing the `Gc` it came from (which the GC treats as a
//! trusted, non-`unsafe` invariant).

use core::fmt::{Debug, Formatter};
use std::borrow::Cow;
use std::marker::PhantomData;

use internment::ArenaIntern;

use crate::chunk::Constant;
use crate::gc::Gc;
use crate::vm::{
    LClosure, LConstant, LValue, NClosure, NativeFunc, Number, Table, Tc, FVec,
};

/// A NuN-boxed Lua value (JavaScriptCore `JSValue` encoding). 8 bytes:
/// a double (`+ 2^49`), a raw untagged heap pointer (type read from an offset-0
/// header), or a small immediate (nil/false/true). `Copy`, since the heap is
/// GC-managed rather than refcounted.
///
/// `'src`/`'intern` are phantom but real bounds: a cell borrows the bytecode and
/// intern arena it points into, so a boxed value cannot outlive them. The
/// payload field is private — see the module docs — which is what lets `unbox`
/// be safe.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LBoxed<'src, 'intern>(u64, PhantomData<Invariant<'src, 'intern>>);

// Phantom for `LBoxed`'s lifetimes. `&'intern &'src ()` is only well-formed when
// `'src: 'intern`, giving `LBoxed` the same implied bound `LValue` gets from its
// `ArenaIntern<'intern, IStr<'src>>` field (needed so `unbox` can rebuild an
// interned string). Wrapping as `fn(T) -> T` makes it invariant in both
// lifetimes — matching the `Tc`/`TCell` it can encode — while staying Send/Sync.
type Invariant<'src, 'intern> = fn(&'intern &'src ()) -> &'intern &'src ();

/// A leaked, non-GC home for a native closure, with the same offset-0 `kind`
/// header as `gc::GcInner` / `IStr`, so `unbox` can identify it from a raw
/// pointer. Kept here because only `box_lvalue`/`unbox` touch it.
#[repr(C)]
pub(crate) struct NClosureCell {
    kind: u8,
    // `pub(crate)` so the JIT's native-identity guard can address it with dynasm's
    // `=> NClosureCell.native` typed offset.
    pub(crate) native: NativeFunc,
}

impl NClosureCell {
    /// Leak a headered cell for `native`. `NClosure` holds the returned pointer
    /// for its whole life, so boxing a native only reads it; the cell is `'static`
    /// and outside the GC, so `Mark` needn't trace it.
    pub(crate) fn leak(native: NativeFunc) -> &'static NClosureCell {
        Box::leak(Box::new(NClosureCell { kind: LBoxed::KIND_NCLOSURE, native }))
    }
}

/// Interned-string arena record. `#[repr(C)]` with `kind` first mirrors
/// `gc::GcInner`'s header, so `unbox` reads the offset-0 tag identically for a raw
/// NuN pointer whether it points at a GC cell or an interned string. `bytes` is a
/// `Cow`: borrowed for a bytecode string constant (zero-copy into the `'src`
/// prototype pool), owned for a runtime-interned string.
#[repr(C)]
#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct IStr<'src> {
    pub kind: u8,
    pub bytes: Cow<'src, [u8]>,
    pub hash: u64,
}

impl<'src> IStr<'src> {
    #[inline(always)]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }
}

impl<'src, 'intern> LBoxed<'src, 'intern> {
    pub const NUMBER_TAG: u64 = 0xfffe_0000_0000_0000;
    pub const DOUBLE_ENCODE_OFFSET: u64 = 0x0002_0000_0000_0000; // 2^49
    pub const OTHER_TAG: u64 = 0x2;
    pub const BOOL_TAG: u64 = 0x4;

    pub const VALUE_NIL: u64 = Self::OTHER_TAG; // 0x2
    pub const VALUE_FALSE: u64 = Self::OTHER_TAG | Self::BOOL_TAG; // 0x6
    pub const VALUE_TRUE: u64 = Self::OTHER_TAG | Self::BOOL_TAG | 1; // 0x7

    /// JSC's `NotCellMask`: a value is a cell (heap pointer) iff none of these
    /// bits are set (no NumberTag bits, no OtherTag bit). Cells are >=8-aligned
    /// with top bits zero, so the pointer is used raw.
    pub const NOT_CELL_MASK: u64 = Self::NUMBER_TAG | Self::OTHER_TAG;

    // Object-header type tags (one byte at offset 0 of every cell, via
    // `gc::CellKind` / `IStr::kind` / `NClosureCell::kind`). `0` = non-cell.
    pub const KIND_TABLE: u8 = 1;
    pub const KIND_LCLOSURE: u8 = 2;
    pub const KIND_NCLOSURE: u8 = 3;
    pub const KIND_OWNED: u8 = 4;
    pub const KIND_INTERNED: u8 = 5;

    /// Canonical quiet NaN, so `+ DOUBLE_ENCODE_OFFSET` never wraps a NaN into
    /// the pointer/immediate range.
    const CANONICAL_NAN: u64 = 0x7ff8_0000_0000_0000;

    pub const NIL: Self = LBoxed(Self::VALUE_NIL, PhantomData);

    /// The raw payload constructor — private, so arbitrary bits can never become
    /// an `LBoxed` from outside this module. This is the crux of `unbox`'s safety.
    #[inline(always)]
    const fn from_raw(v: u64) -> Self {
        LBoxed(v, PhantomData)
    }

    /// Read-only access to the raw payload (for identity comparisons/hashing).
    #[inline(always)]
    pub fn bits(&self) -> u64 {
        self.0
    }

    #[inline(always)]
    pub fn from_number(n: f64) -> Self {
        let bits = if n.is_nan() { Self::CANONICAL_NAN } else { n.to_bits() };
        Self::from_raw(bits.wrapping_add(Self::DOUBLE_ENCODE_OFFSET))
    }

    #[inline(always)]
    pub fn from_bool(b: bool) -> Self {
        Self::from_raw(if b { Self::VALUE_TRUE } else { Self::VALUE_FALSE })
    }

    /// Box an already-canonical interned string handle.
    #[inline(always)]
    pub fn interned(s: ArenaIntern<'intern, IStr<'src>>) -> Self {
        Self::from_raw(s.into_ref() as *const IStr as u64)
    }

    #[inline(always)]
    pub fn is_number(&self) -> bool {
        (self.0 & Self::NUMBER_TAG) != 0
    }

    /// Decode a number, or `None` if this value isn't a number.
    #[inline(always)]
    pub fn as_number(&self) -> Option<f64> {
        if self.is_number() {
            Some(f64::from_bits(self.0.wrapping_sub(Self::DOUBLE_ENCODE_OFFSET)))
        } else {
            None
        }
    }

    /// Lua truthiness: only `nil` and `false` are falsy.
    #[inline(always)]
    pub fn truthy(&self) -> bool {
        self.0 != Self::VALUE_NIL && self.0 != Self::VALUE_FALSE
    }

    /// The `Tc<Table>` if this is a table, else `None`. `unbox` is
    /// `inline(always)` and this matches a single variant, so it folds to the
    /// tag check `NotCellMask==0 && kind==TABLE`.
    #[inline(always)]
    pub fn as_table(&self) -> Option<Tc<Table<'src, 'intern>>> {
        // Pin the decode to `'src`/`'intern`: `Tc` is invariant.
        let v: LValue<'src, 'intern> = self.unbox();
        match v {
            LValue::Table(t) => Some(t),
            _ => None,
        }
    }

    /// Box an `LValue` into its `u64` representation. Every case is a plain, cheap
    /// conversion.
    #[inline(always)]
    pub fn box_lvalue(val: LValue<'src, 'intern>) -> Self {
        match val {
            LValue::Nil => Self::NIL,
            LValue::Bool(b) => Self::from_bool(b),
            LValue::Number(n) => Self::from_number(n.0),
            // Cells box as their raw, untagged pointer; the type lives in the
            // object's offset-0 `kind` header (see gc::CellKind).
            LValue::Table(t) => Self::from_raw(t.0.to_addr()),
            LValue::LClosure(c) => Self::from_raw(c.0.to_addr()),
            // The native's headered cell already exists (leaked at `NClosure::new`).
            LValue::NClosure(n) => Self::from_raw(n.cell as *const NClosureCell as u64),
            LValue::InternedString(s) => Self::interned(s),
            LValue::OwnedString(s) => Self::from_raw(s.to_addr()),
        }
    }

    /// Decode into the `LValue` view. The single place that reads the object
    /// header / transmutes; everything else goes through here + a `match`.
    ///
    /// Safe because the payload is private (module docs): every `LBoxed` was
    /// produced by a safe constructor from a live value, so `bits` always encodes
    /// a live object of the tagged type. Reconstructing its `Gc` is then exactly
    /// as sound as dereferencing that `Gc` — the GC's trusted liveness invariant,
    /// checked under `gc_sanitize`.
    #[inline(always)]
    pub fn unbox(&self) -> LValue<'src, 'intern> {
        let bits = self.0;
        if bits & Self::NUMBER_TAG != 0 {
            return LValue::Number(Number(f64::from_bits(bits.wrapping_sub(Self::DOUBLE_ENCODE_OFFSET))));
        }
        if bits & Self::NOT_CELL_MASK != 0 {
            return match bits {
                Self::VALUE_NIL => LValue::Nil,
                Self::VALUE_FALSE => LValue::Bool(false),
                Self::VALUE_TRUE => LValue::Bool(true),
                _ => unsafe { std::hint::unreachable_unchecked() },
            };
        }
        // SAFETY: `bits` is a live cell pointer of the kind its header records
        // (upheld by the sealed constructors).
        match unsafe { crate::gc::read_cell_kind(bits) } {
            Self::KIND_TABLE => LValue::Table(Tc(unsafe { Gc::from_addr(bits) })),
            Self::KIND_LCLOSURE => LValue::LClosure(Tc(unsafe { Gc::from_addr(bits) })),
            Self::KIND_NCLOSURE => LValue::NClosure(NClosure { cell: unsafe { &*(bits as *const NClosureCell) } }),
            Self::KIND_OWNED => LValue::OwnedString(unsafe { Gc::from_addr(bits) }),
            Self::KIND_INTERNED => {
                let ptr = bits as *const IStr<'src>;
                LValue::InternedString(unsafe { std::mem::transmute(ptr) })
            }
            _ => unsafe { std::hint::unreachable_unchecked() },
        }
    }
}

impl Default for LBoxed<'_, '_> {
    #[inline(always)]
    fn default() -> Self {
        Self::NIL
    }
}

// `LBoxed` intentionally does NOT implement `Eq`/`Hash`: it can hold an owned
// string, for which bit equality would be wrong (equal content, different
// pointers) and content equality would be slow and need an `owner`. Values that
// need `Eq`/`Hash` use the canonical `LCanon` wrapper in `vm` instead.
impl Debug for LBoxed<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}", self.unbox())
    }
}

impl<'src, 'intern> From<&LConstant<'src, 'intern>> for LBoxed<'src, 'intern> {
    /// Constants never contain owned strings (string constants are interned by
    /// `globally_intern`), so an interned string constant is already canonical.
    #[inline]
    fn from(value: &LConstant<'src, 'intern>) -> Self {
        match value {
            Constant::Nil => Self::NIL,
            Constant::Bool(b) => Self::from_bool(*b),
            Constant::Number(n) => Self::from_number(n.0),
            Constant::String(s) => Self::interned(*s),
        }
    }
}
