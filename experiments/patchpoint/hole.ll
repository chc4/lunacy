; Patchpoint / stackmap wrappers for the stencil-hole experiment
; (`just patchpoint-experiment`). Rust cannot call the vararg
; `llvm.experimental.*` intrinsics itself, so each wrapper is an ordinary
; non-vararg function that the Rust side declares `extern "C"`; cross-language
; LTO is expected to inline it into the Rust caller, so the patchpoint lands in
; the Rust function's body. A patchpoint's ID must be a constant, so there is
; one wrapper per hole.

target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

declare i64 @llvm.experimental.patchpoint.i64(i64, i32, ptr, i32, ...)
declare void @llvm.experimental.stackmap(i64, i32, ...)

; anyregcc: LLVM picks the result register and records it in the stackmap.
; 10 reserved bytes: room for `movabs r64, imm64`.
define linkonce_odr i64 @pp_anyreg0() alwaysinline {
  %r = call anyregcc i64 (i64, i32, ptr, i32, ...) @llvm.experimental.patchpoint.i64(i64 100, i32 10, ptr null, i32 0)
  ret i64 %r
}
define linkonce_odr i64 @pp_anyreg1() alwaysinline {
  %r = call anyregcc i64 (i64, i32, ptr, i32, ...) @llvm.experimental.patchpoint.i64(i64 101, i32 10, ptr null, i32 0)
  ret i64 %r
}

; Same with 6 reserved bytes: room for `mov r32, imm32` (6 with a REX prefix).
define linkonce_odr i64 @pp_anyreg_small() alwaysinline {
  %r = call anyregcc i64 (i64, i32, ptr, i32, ...) @llvm.experimental.patchpoint.i64(i64 102, i32 6, ptr null, i32 0)
  ret i64 %r
}

; C calling convention: the result is in rax, and every caller-saved register
; is clobbered across the site (it is a call as far as regalloc knows).
define linkonce_odr i64 @pp_ccc0() alwaysinline {
  %r = call ccc i64 (i64, i32, ptr, i32, ...) @llvm.experimental.patchpoint.i64(i64 200, i32 13, ptr null, i32 0)
  ret i64 %r
}

; A stackmap has no result; it only records where live values are at a point.
; Here it records where `%x` lives, with 8 shadow bytes.
define linkonce_odr void @sm_record(i64 %x) alwaysinline {
  call void (i64, i32, ...) @llvm.experimental.stackmap(i64 300, i32 8, i64 %x)
  ret void
}
