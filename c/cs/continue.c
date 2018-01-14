#include <stdio.h>

int for_with_continue()
{
    int sum = 0;
    int i;
    for (i = 0; i < 10; ++i) {
        if (i & 1) 
            continue;   /* skip odd i's */
        sum += i;
    }

    return sum;
}
/*
	movl	$0, %edx                # edx = 0 (i)
	movl	$0, %eax                # eax = 0 (sum)
.L3:
	movl	%edx, %esi              # esi = edx
	andl	$1, %esi                # esi = esi & 1
	leal	(%rax,%rdx), %ecx       # ecx = eax + edx (potential new eax)
	testl	%esi, %esi              # test esi
	cmove	%ecx, %eax              # if zero eax = ecx
	addl	$1, %edx                # edx = edx + 1
	cmpl	$10, %edx               # compare edx with 10
	jne	.L3                         # jump (n)on-(e)qual
	rep ret
*/    

int for_with_continue_goto()
{
    int sum = 0;
    int i = 0;
    if (!(i < 10))
        goto done;
loop:
    if (i & 1) 
        goto loop_end;
    sum += i;
loop_end:
    ++i;
    if (i < 10)
        goto loop;
done:
    return sum;
}
/*
	movl	$0, %edx
	movl	$0, %eax
.L6:
	movl	%edx, %esi
	andl	$1, %esi
	leal	(%rax,%rdx), %ecx
	testl	%esi, %esi
	cmove	%ecx, %eax
.L7:
	addl	$1, %edx
	cmpl	$10, %edx
	jne	.L6
	rep ret
*/


int main() {

    printf("sum = %d\n", for_with_continue());
    /* 2 + 4 + 6 + 8 = 20 */
    printf("sum = %d\n", for_with_continue_goto());

    return 0;
}
