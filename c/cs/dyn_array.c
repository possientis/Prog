/* argument n should appear before int A[n][n] */
int elem (int n, int A[n][n], int i, int j) {
    return A[i][j];
}

/*
	movslq	%edx, %rdx              # rdx = i       (signed extended)
	salq	$2, %rdx                # rdx = i*4
	movslq	%edi, %rdi              # rdi = n       (signed extended)
	imulq	%rdi, %rdx              # rdx = i*4*n   (offset row i)
	movslq	%ecx, %rcx              # rcx = j       (signed extended)
	leaq	(%rsi,%rcx,4), %rax     # rax = A + 4*j
	movl	(%rax,%rdx), %eax       # eax = *(A + 4*j + i*4*n)
	ret
*/
	
