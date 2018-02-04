#include <stdio.h>

void sfact_helper(long x, long *resultp)
{   
    if (x <= 1)
        *resultp = 1;
    else {
        long nresult;
        sfact_helper(x-1,&nresult);
        *resultp = x * nresult;
    }
}
/*  callee saved registers are : rbx, rbp, r12, r13, r14, r15
 *
	cmpq	$1, %rdi            # compare x to 1
	jle	.L7                     # if <= then goto .L7
	pushq	%rbp                # rbp callee saved
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	pushq	%rbx                # rbx callee saved
	.cfi_def_cfa_offset 24
	.cfi_offset 3, -24
	subq	$24, %rsp           # 24 bytes allocated to stack frame
	.cfi_def_cfa_offset 48
	movq	%rsi, %rbp          # rbp = resultp
	movq	%rdi, %rbx          # rbx = x
	leaq	8(%rsp), %rsi       # rsi = rsp + 8 (&nresult) (2nd argument)
	leaq	-1(%rdi), %rdi      # rdi = rdi - 1            (1st argument)
	call	sfact_helper        # rbx, rbp, rsp preserved across calls
	imulq	8(%rsp), %rbx       # rbx = x * nresult 
	movq	%rbx, 0(%rbp)       # *resultp = rbx
	addq	$24, %rsp           # deallocating stack space
	.cfi_def_cfa_offset 24
	popq	%rbx                # restoring rbx
	.cfi_restore 3
	.cfi_def_cfa_offset 16
	popq	%rbp                # restoring rbp
	.cfi_restore 6
	.cfi_def_cfa_offset 8
	ret
.L7:
	movq	$1, (%rsi)       # *resultp = 1
	ret
*/
	
long sfact(long x)
{
    long result;
    sfact_helper(x,&result);
    return result;
}


int main() 
{
    printf("5! = %ld\n", sfact(5));

    return 0;
}
