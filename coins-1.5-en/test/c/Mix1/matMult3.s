 .ident "Coins Compiler version: coins-1.4.3.1 + BackEnd-1.0"
/* JavaCG for target:x86 convention:cygwin */

	.text
	.align	4
___sgetc:
	pushl	%ebp
	movl	%esp,%ebp
	pushl	%ebx
	pushl	%esi
	movl	8(%ebp),%esi
	movl	4(%esi),%eax
	leal	-1(%eax),%eax
	movl	%eax,4(%esi)
	movl	4(%esi),%eax
	cmpl	$0,%eax
	jge	.L4
.L3:
	pushl	%esi
	call	___srget
	movl	%eax,%ebx
	leal	4(%esp),%esp
	jmp	.L5
.L4:
	movl	(%esi),%eax
	movzbl	(%eax),%ebx
	movl	(%esi),%eax
	leal	1(%eax),%eax
	movl	%eax,(%esi)
.L5:
	movswl	12(%esi),%eax
	andl	$16384,%eax
	cmpl	$0,%eax
	je	.L18
.L6:
	cmpl	$13,%ebx
	jne	.L8
.L7:
	movl	$1,%eax
	jmp	.L9
.L8:
	movl	$0,%eax
.L9:
	movw	%ax,%ax
	movswl	%ax,%eax
	cmpl	$0,%eax
	je	.L18
.L10:
	movl	4(%esi),%eax
	leal	-1(%eax),%eax
	movl	%eax,4(%esi)
	movl	4(%esi),%eax
	cmpl	$0,%eax
	jge	.L12
.L11:
	pushl	%esi
	call	___srget
	leal	4(%esp),%esp
	jmp	.L13
.L12:
	movl	(%esi),%eax
	movzbl	(%eax),%eax
	movl	(%esi),%ecx
	leal	1(%ecx),%ecx
	movl	%ecx,(%esi)
.L13:
	cmpl	$10,%eax
	jne	.L15
.L14:
	movl	%eax,%ebx
	jmp	.L18
.L15:
	pushl	%esi
	pushl	%eax
	call	_ungetc
	leal	8(%esp),%esp
.L18:
	movl	%ebx,%eax
	popl	%esi
	popl	%ebx
	leave
	ret


	.align	4
	.global	_multiply
_multiply:
	pushl	%ebp
	movl	%esp,%ebp
	subl	$8,%esp
	pushl	%ebx
	pushl	%esi
	pushl	%edi
	movl	8(%ebp),%eax
	movl	%eax,-8(%ebp)
	movl	12(%ebp),%esi
	movl	16(%ebp),%ebx
	movl	$0,%ecx
.L22:
	cmpl	$500,%ecx
	jge	.L30
.L23:
	movl	$0,%edx
.L24:
	cmpl	$500,%edx
	jge	.L29
.L25:
	fldz
	fstps	-4(%ebp)
	movl	$0,%eax
.L26:
	cmpl	$500,%eax
	jge	.L28
.L27:
	movl	%ecx,%edi
	imull	$2000,%edi
	leal	(%esi,%edi),%edi
	flds	(%edi,%eax,4)
	movl	%eax,%edi
	imull	$2000,%edi
	leal	(%ebx,%edi),%edi
	fmuls	(%edi,%edx,4)
	flds	-4(%ebp)
	faddp	%st,%st(1)
	fstps	-4(%ebp)
	leal	1(%eax),%eax
	jmp	.L26
.L28:
	movl	%ecx,%eax
	imull	$2000,%eax
	addl	-8(%ebp),%eax
	flds	-4(%ebp)
	fstps	(%eax,%edx,4)
	leal	1(%edx),%edx
	jmp	.L24
.L29:
	leal	1(%ecx),%ecx
	jmp	.L22
.L30:
	popl	%edi
	popl	%esi
	popl	%ebx
	leave
	ret

	.align	1
_string.23:
	.byte	10
	.byte	105
	.byte	61
	.byte	37
	.byte	100
	.byte	32
	.byte	0
	.align	1
_string.25:
	.byte	32
	.byte	37
	.byte	55
	.byte	46
	.byte	50
	.byte	102
	.byte	0

	.align	4
	.global	_main
_main:
	pushl	%ebp
	movl	%esp,%ebp
	subl	$4,%esp
	pushl	%ebx
	pushl	%esi
	movl	$0,%ebx
.L33:
	cmpl	$500,%ebx
	jge	.L38
.L34:
	movl	$0,%esi
.L35:
	cmpl	$500,%esi
	jge	.L37
.L36:
	call	_rand
	movl	$214748365,%ecx
	cdq
	idivl	%ecx
	movl	%eax,-4(%ebp)
	fildl	-4(%ebp)
	movl	%ebx,%eax
	imull	$2000,%eax
	fstps	_a.14(%eax,%esi,4)
	leal	1(%esi),%esi
	jmp	.L35
.L37:
	leal	1(%ebx),%ebx
	jmp	.L33
.L38:
	movl	$0,%ebx
.L39:
	cmpl	$500,%ebx
	jge	.L44
.L40:
	movl	$0,%esi
.L41:
	cmpl	$500,%esi
	jge	.L43
.L42:
	call	_rand
	movl	$214748365,%ecx
	cdq
	idivl	%ecx
	movl	%eax,-4(%ebp)
	fildl	-4(%ebp)
	movl	%ebx,%eax
	imull	$2000,%eax
	fstps	_b.15(%eax,%esi,4)
	leal	1(%esi),%esi
	jmp	.L41
.L43:
	leal	1(%ebx),%ebx
	jmp	.L39
.L44:
	pushl	$_b.15
	pushl	$_a.14
	pushl	$_c.16
	call	_multiply
	leal	12(%esp),%esp
	movl	$0,%ebx
.L45:
	cmpl	$10,%ebx
	jge	.L50
.L46:
	pushl	%ebx
	pushl	$_string.23
	call	_printf
	leal	8(%esp),%esp
	movl	$0,%esi
.L47:
	cmpl	$10,%esi
	jge	.L49
.L48:
	movl	%ebx,%eax
	imull	$2000,%eax
	flds	_c.16(%eax,%esi,4)
	sub	$8,%esp
	fstpl	(%esp)
	pushl	$_string.25
	call	_printf
	leal	12(%esp),%esp
	leal	1(%esi),%esi
	jmp	.L47
.L49:
	leal	1(%ebx),%ebx
	jmp	.L45
.L50:
	movl	$0,%eax
	popl	%esi
	popl	%ebx
	leave
	ret

	.data
	.align	4
_a.14:
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.align	4
_b.15:
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.align	4
_c.16:
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000
	.skip	2000