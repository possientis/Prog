
void proc(long,long*,int,int*,short,short*,char,char*);

/* order: rdi,rsi,rdx,rcx,r8,r9 */
/* 7th and 8th argument pushed on the stack, starting with 8th */

long int call_proc()
{
    long  x1 = 1;
    int   x2 = 2;
    short x3 = 3;
    char  x4 = 4;
    proc(x1,&x1,x2,&x2,x3,&x3,x4,&x4);
    return (x1 + x2)*(x3 - x4);
}

/*  16 general purpose registers
 *  6 are designated for passing arguments: rdi,rsi,rdx,rcx,r8,r9
 *  6 are callee saved temporary: rbx,rbp,r12,r13,r14,r15
 *  1 holds the return value: rax
 *  1 serves as stack pointer: rsp
 *  2 are caller saved: r10 and r11

 * on return from calling the procedure 'proc', the code does not 
 * rely on any register value having been preserved except rsp.

	subq	$24, %rsp               # 24 bytes allocated to stack frame
	.cfi_def_cfa_offset 32
	movq	$1, 8(%rsp)             # x1 : rsp+8,rsp+9,rsp+10,rsp+11,...,rsp+15
	movl	$2, 4(%rsp)             # x2 : rsp+4,rsp+5,rsp+6,rsp+7
	movw	$3, 2(%rsp)             # x3 : rsp+2,rsp+3
	movb	$4, 1(%rsp)             # x4 : rsp+1
	leaq	4(%rsp), %rcx           # 4th argument in rcx (&x2)
	leaq	8(%rsp), %rsi           # 2nd argument in rsi (&x1)
	leaq	1(%rsp), %rax           # rax = &x4
	pushq	%rax                    # 8th argument pushed on stack
	.cfi_def_cfa_offset 40
	pushq	$4                      # 7th argument pushed on stack 
	.cfi_def_cfa_offset 48
	leaq	18(%rsp), %r9           # 6th argument in r9 (rsp+18 now &x3)
	movl	$3, %r8d                # 5th argument in r8
	movl	$2, %edx                # 3th argument in rdx
	movl	$1, %edi                # 1st argument in rdi
	call	proc@PLT                 
	movslq	20(%rsp), %rax          # rax = (long) x2
	addq	24(%rsp), %rax          # rax = rax + x1
	movswl	18(%rsp), %edx          # edx = (int) x3
	movsbl	17(%rsp), %ecx          # ecx = (int) x4
	subl	%ecx, %edx              # edx = x3 - x4  (int subtraction)
	movslq	%edx, %rdx              # rdx = (long) (x3 - x4)
	imulq	%rdx, %rax              # rax = rax * rdx
	addq	$40, %rsp               # restore stack pointer (16 (2 pushes) + 24)
	.cfi_def_cfa_offset 8
	ret
*/
	

