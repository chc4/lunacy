; Holes as absolute symbols, for `just absolute-hole-experiment`. A global with
; `!absolute_symbol` is one whose address LLVM takes as a constant in the range
; given, so it can be an instruction's immediate operand even in a PIE. Rust
; cannot attach the metadata, so it never declares the holes: it calls these
; accessors, which cross-language LTO inlines, leaving the annotated declaration
; the only one.

target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; A 32-bit hole, signed: its address fits `imm32` sign-extended to 64 bits.
@__lunacy_abs_hole1 = extern_weak global i8, !absolute_symbol !0
; A byte-sized hole: room for `imm8`.
@__lunacy_abs_hole2 = extern_weak global i8, !absolute_symbol !1

!0 = !{i64 0, i64 2147483648}
!1 = !{i64 0, i64 128}

define linkonce_odr i32 @hole1_u32() alwaysinline {
  ret i32 ptrtoint (ptr @__lunacy_abs_hole1 to i32)
}
define linkonce_odr i64 @hole1_u64() alwaysinline {
  ret i64 ptrtoint (ptr @__lunacy_abs_hole1 to i64)
}
define linkonce_odr i32 @hole2_u32() alwaysinline {
  ret i32 ptrtoint (ptr @__lunacy_abs_hole2 to i32)
}
