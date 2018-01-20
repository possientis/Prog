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

/*  switch implemented with a 'jump table' -> o(1) search for n
	subl	$100, %esi              # n = n - 100 
	cmpl	$6, %esi                # compare n with 6 
	ja	.L8                         # jump (a)bove -> unsigned comparison
	movl	%esi, %esi              # esi = esi (why is this useful ? )
	leaq	.L4(%rip), %rdx         # rdx = base address of table (point .L4)
	movslq	(%rdx,%rsi,4), %rax     # rax = *(base + n*4) (relevant offset)
	addq	%rdx, %rax              # rax = base + offset (addr of code)
	jmp	*%rax                       # jump to address in rax 
	.section	.rodata             # (r)ead-(o)nly data starts here
	.align 4
	.align 4
.L4:                                # gcc creates a 'jump table'
	.long	.L3-.L4                 # n = 0, jump to .L3
	.long	.L8-.L4                 # n = 1, jump to .L8 (default)
	.long	.L5-.L4                 # n = 2, jump to .L5
	.long	.L6-.L4                 # n = 3, jump to .L6
	.long	.L7-.L4                 # n = 4, jump to .L7
	.long	.L8-.L4                 # n = 5, jump to .L8
	.long	.L7-.L4                 # n = 6, jump to .L7
	.text
.L3:
	leal	(%rdi,%rdi,2), %eax     # eax = x + 2*x 
	leal	(%rdi,%rax,4), %eax     # eax = x + 4*eax (net eax = 13*x)
	ret                             # break effectively ends function
.L5:
	addl	$10, %edi               # x = x + 10 (but no 'break;')
.L6:
	leal	11(%rdi), %eax          # eax = x + 11
	ret                             # break this time
.L7:
	movl	%edi, %eax              # eax = x
	imull	%edi, %eax              # eax = eax * x (net eax = x * x)
	ret                             # break
.L8:
	movl	$0, %eax                # defaulf case
	ret
*/
