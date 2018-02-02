long gfun(int x, int y) 
{
    long t1 = (long) x + y;     /* 64 bits addition */
    long t2 = (long) (x + y);   /* 32 bits addition */
    return t1 | t2;
}

/*
 * 	movslq	%edi, %rax          # rax = (long) x;
	movslq	%esi, %rdx          # rdx = (long) y;
	addq	%rax, %rdx          # rdx = rax + rdx   -> t1
	addl	%esi, %edi          # edi = x + y 
	movslq	%edi, %rax          # rax = (long) edi  -> t2 
	orq	%rdx, %rax              # rax = t1 | t2
	ret
*/


long ex348 (int a, char b, long c, int d) {
    return a*b + c*d;
}
/*
	movsbl	%sil, %esi
	imull	%esi, %edi
	movslq	%edi, %rdi
	movslq	%ecx, %rax
	imulq	%rax, %rdx
	leaq	(%rdi,%rdx), %rax
	ret
*/	

void proc
    ( long a1   , long  *a1p
    , int a2    , int   *a2p
    , short a3  , short *a3p
    , char a4   , char  *a4p 
    ) 
{
    *a1p += a1;
    *a2p += a2;
    *a3p += a3;
    *a4p += a4;
}
        
/* 	movq	16(%rsp), %rax      # rax = a4p
	addq	%rdi, (%rsi)        # *ap1 += a1
	addl	%edx, (%rcx)        # *a2p += a2
	addw	%r8w, (%r9)         # *a3p += a3;
	movl	8(%rsp), %edx       # dl = a4
	addb	%dl, (%rax)         # *a4p += a4
	ret		
*/
