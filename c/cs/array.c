#define M 3
#define N 4


int mat1[M][N];
int mat2[N][M];



int sum_element(int i, int j) {
    return mat1[i][j] + mat2[j][i];
}

/*
	movslq	%esi, %rsi                  # rsi = j (signed extended)
	movslq	%edi, %rdi                  # rdi = i (signed extended) 
	leaq	(%rsi,%rdi,4), %rcx         # rcx = j + 4*i  
	leaq	(%rsi,%rsi,2), %rax         # rax = 3*j 
	addq	%rax, %rdi                  # rdi = i + 3*j
	leaq	mat2(%rip), %rax            # rax = mat2
	movl	(%rax,%rdi,4), %eax         # eax = mat2 + 4*(i + 3*j)
	leaq	mat1(%rip), %rdx            # rdx = mat1
	addl	(%rdx,%rcx,4), %eax         # eax += mat1 + 4*(j + 4*i)
	ret
*/
	
