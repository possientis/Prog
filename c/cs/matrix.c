#define N 16

typedef int matrix[N][N];


int prod(matrix a, matrix b, int i, int j) {
    int k;
    int sum = 0;
    for(k = 0; k < N; ++k)
        sum += a[i][k]*b[k][j];
    return sum;
}

/* order is rdi, rsi, rdx, rcx, r8, r9 */

/*
    movslq	%edx, %rdx                  # rdx =  i      (signed extended)
	salq	$6, %rdx                    # rdx =  i*64   (16 (col size) * 4 (int)
	addq	%rdx, %rdi                  # rdi =  a + i*64 (start of row i of a)
	movslq	%ecx, %rax                  # rax =  j      (signed extended)
	salq	$2, %rax                    # rax =  j*4    (int size)
	leaq	(%rsi,%rax), %rdx           # rdx =  b + j*4 (start of col j of b)
	leaq	1024(%rsi,%rax), %rsi       # rsi =  b + j*4 + 1024 (end of col)
	movl	$0, %eax                    # sum = 0
.L2:
	movl	(%rdi), %ecx                # ecx = (%rdi)
	imull	(%rdx), %ecx                # ecx = ecx * (%rdx)
	addl	%ecx, %eax                  # sum += ecx
	addq	$4, %rdi                    # rdi += 4  (next int on row i) 
	addq	$64, %rdx                   # rdx += 64 (next int on col j) 
	cmpq	%rsi, %rdx                  # compare rdx to rsi
	jne	.L2                             # if rdx <> rsi goto .L2
	rep ret                             # return sum
*/
