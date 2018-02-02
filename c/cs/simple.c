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


long gval1 = 567;
long gval2 = 763;

long simple_call_l()
{
    long z = simple_l(&gval1,12L);
    return z + gval2;
} 
	
int main() {
    simple_call_l();
    return 0;
}

	
