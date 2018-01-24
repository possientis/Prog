long simple_l(long *xp, long y) 
{
    long t = *xp + y;
    *xp = t;
    return t;
}

/*	
 *	movq	%rsi, %rax          # rax = y
	addq	(%rdi), %rax        # rax = *xp + rax
	movq	%rax, (%rdi)        # *xp = rax
	ret
*/

/*  compiled with -m32 option
 *
 *	movl	4(%esp), %edx       # edx = xp
	movl	(%edx), %eax        # eax = *xp 
	addl	8(%esp), %eax       # eax = eax + y
	movl	%eax, (%edx)        # *xp = eax
	ret
*/



	


	
