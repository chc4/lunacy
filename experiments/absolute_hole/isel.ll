; Which operations x86 instruction selection folds an `!absolute_symbol` hole
; into as an immediate, with no Rust or LTO involved: `llc` on this alone
; (`just absolute-hole-isel`).

target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@h32 = external global i8, !absolute_symbol !0
@h8 = external global i8, !absolute_symbol !1
@hfull = external global i8, !absolute_symbol !2

!0 = !{i64 0, i64 2147483648}
!1 = !{i64 0, i64 128}
!2 = !{i64 -1, i64 -1}

define i32 @sub32(i32 %x) {
  %r = sub i32 %x, ptrtoint (ptr @h32 to i32)
  ret i32 %r
}
define i32 @add32(i32 %x) {
  %r = add i32 %x, ptrtoint (ptr @h32 to i32)
  ret i32 %r
}
define i32 @add8(i32 %x) {
  %r = add i32 %x, ptrtoint (ptr @h8 to i32)
  ret i32 %r
}
define i64 @and64(i64 %x) {
  %r = and i64 %x, ptrtoint (ptr @h32 to i64)
  ret i64 %r
}
define i64 @add64(i64 %x) {
  %r = add i64 %x, ptrtoint (ptr @h32 to i64)
  ret i64 %r
}
define i1 @cmp32(i32 %x) {
  %r = icmp ult i32 %x, ptrtoint (ptr @h32 to i32)
  ret i1 %r
}
define i32 @sub32full(i32 %x) {
  %r = sub i32 %x, ptrtoint (ptr @hfull to i32)
  ret i32 %r
}
