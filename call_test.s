	.file	"call_test.38c1e54e1b9de473-cgu.0"
	.section	.text._RNCNvCs4S7kSKZfn8d_9call_test7call_it0B3_,"ax",@progbits
	.p2align	4
	.type	_RNCNvCs4S7kSKZfn8d_9call_test7call_it0B3_,@function
_RNCNvCs4S7kSKZfn8d_9call_test7call_it0B3_:
	.cfi_startproc
	retq
.Lfunc_end0:
	.size	_RNCNvCs4S7kSKZfn8d_9call_test7call_it0B3_, .Lfunc_end0-_RNCNvCs4S7kSKZfn8d_9call_test7call_it0B3_
	.cfi_endproc

	.section	.text._RNSNvYNCNvCs4S7kSKZfn8d_9call_test7call_it0INtNtNtCs5Ilh7FIrOrP_4core3ops8function6FnOnceuE9call_once6vtableB8_,"ax",@progbits
	.p2align	4
	.type	_RNSNvYNCNvCs4S7kSKZfn8d_9call_test7call_it0INtNtNtCs5Ilh7FIrOrP_4core3ops8function6FnOnceuE9call_once6vtableB8_,@function
_RNSNvYNCNvCs4S7kSKZfn8d_9call_test7call_it0INtNtNtCs5Ilh7FIrOrP_4core3ops8function6FnOnceuE9call_once6vtableB8_:
	.cfi_startproc
	retq
.Lfunc_end1:
	.size	_RNSNvYNCNvCs4S7kSKZfn8d_9call_test7call_it0INtNtNtCs5Ilh7FIrOrP_4core3ops8function6FnOnceuE9call_once6vtableB8_, .Lfunc_end1-_RNSNvYNCNvCs4S7kSKZfn8d_9call_test7call_it0INtNtNtCs5Ilh7FIrOrP_4core3ops8function6FnOnceuE9call_once6vtableB8_
	.cfi_endproc

	.section	.text._RNvCs4S7kSKZfn8d_9call_test7call_it,"ax",@progbits
	.globl	_RNvCs4S7kSKZfn8d_9call_test7call_it
	.p2align	4
	.type	_RNvCs4S7kSKZfn8d_9call_test7call_it,@function
_RNvCs4S7kSKZfn8d_9call_test7call_it:
	.cfi_startproc
	pushq	%rax
	.cfi_def_cfa_offset 16
	movq	%rsi, %rax
	leaq	.Lanon.913c21b43eafda0e01a7fcebdbe6485d.0(%rip), %r8
	leaq	7(%rsp), %rcx
	movq	%rcx, %rsi
	movq	%rcx, %rdx
	callq	*40(%rax)
	popq	%rax
	.cfi_def_cfa_offset 8
	retq
.Lfunc_end2:
	.size	_RNvCs4S7kSKZfn8d_9call_test7call_it, .Lfunc_end2-_RNvCs4S7kSKZfn8d_9call_test7call_it
	.cfi_endproc

	.type	.Lanon.913c21b43eafda0e01a7fcebdbe6485d.0,@object
	.section	.data.rel.ro..Lanon.913c21b43eafda0e01a7fcebdbe6485d.0,"aw",@progbits
	.p2align	3, 0x0
.Lanon.913c21b43eafda0e01a7fcebdbe6485d.0:
	.asciz	"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000"
	.quad	_RNSNvYNCNvCs4S7kSKZfn8d_9call_test7call_it0INtNtNtCs5Ilh7FIrOrP_4core3ops8function6FnOnceuE9call_once6vtableB8_
	.quad	_RNCNvCs4S7kSKZfn8d_9call_test7call_it0B3_
	.size	.Lanon.913c21b43eafda0e01a7fcebdbe6485d.0, 40

	.ident	"rustc version 1.97.0-nightly (8b03437a8 2026-05-12)"
	.section	".note.GNU-stack","",@progbits
