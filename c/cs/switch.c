int switch_eg(int x, int n) {
    int result = x;

    switch(n){

        case 100: 
            result *= 13;
            break;

        case 102:
            result += 10;
            /* fall through */

        case 103:
            result += 11;
            break;

        case 104:
        case 106:
            result *= result;
            break;

        default:
            result = 0;
    }
    
    return result;
}

/*
	subl	$100, %esi              # n = n - 1 
	cmpl	$6, %esi                # compare n with 6 
	ja	.L8                         # jump (a)bove -> unsigned comparison
	movl	%esi, %esi              # esi = esi (why is this useful ? )
	leaq	.L4(%rip), %rdx         # rdx = TODO 
	movslq	(%rdx,%rsi,4), %rax
	addq	%rdx, %rax
	jmp	*%rax
	.section	.rodata
	.align 4
	.align 4
.L4:
	.long	.L3-.L4
	.long	.L8-.L4
	.long	.L5-.L4
	.long	.L6-.L4
	.long	.L7-.L4
	.long	.L8-.L4
	.long	.L7-.L4
	.text
.L3:
	leal	(%rdi,%rdi,2), %eax
	leal	(%rdi,%rax,4), %eax
	ret
.L5:
	addl	$10, %edi
.L6:
	leal	11(%rdi), %eax
	ret
.L7:
	movl	%edi, %eax
	imull	%edi, %eax
	ret
.L8:
	movl	$0, %eax
	ret
*/
