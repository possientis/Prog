#include <stdio.h>

/* n <= 0 ???? */

int fact_do(int n)
{
    int result = 1;

    do {
        result *= n;
        n = n - 1;
    } while (n > 1);

    return result;
}
/*

	movl	$1, %eax
.L2:
	imull	%edi, %eax
	subl	$1, %edi
	cmpl	$1, %edi
	jg	.L2             # jump '(g)reater' => signed comparison
	rep ret
	
*/

long fact_do2(int n)
{
    long result = 1L;

    do {

        result *= (long) n;
        n = n - 1;
    } while (n > 1);

    return result;
}

/*
	movl	$1, %eax
.L5:
	movslq	%edi, %rdx      # converting n to long -> rdx
	imulq	%rdx, %rax      # 64 bits multiplication
	subl	$1, %edi
	cmpl	$1, %edi
	jg	.L5
	rep ret
*/


int fact_while(int n)
{
    int result = 1;
    while (n > 1) {
        result *= n;
        n = n - 1;
    }
    return result;
}
/*
	cmpl	$1, %edi        # compare n with 1 
	jle	.L10                # jump (l)ess or (e)qual -> signed comparison
	movl	$1, %eax        # eax = 1
.L9:
	imull	%edi, %eax      # eax = eax * n 
	subl	$1, %edi        # n = n - 1
	cmpl	$1, %edi        # compare n with 1
	jne	.L9                 # jump (n)on (e)equal 
	rep ret                 # return eax
.L10:
	movl	$1, %eax        # eax = 1
	ret                     # return eax
*/

int fact_while_goto(int n)
{
    int result = 1;
    if (n <= 1)
        goto done;
loop:
    result *= n;
    n = n - 1;
    if (n > 1)
        goto loop;
done:
    return result;
}

/*
    cmpl	$1, %edi        # 
	jle	.L15
	movl	$1, %eax
.L14:
	imull	%edi, %eax
	subl	$1, %edi
	cmpl	$1, %edi
	jne	.L14                # compiles as if condition is (n != 1)
	rep ret
.L15:
	movl	$1, %eax
.L13:
	ret
*/


int fact_for(int n)
{
    int i;
    int result = 1;
    for(i = 2; i <= n; ++i)
        result *= i;
    return result;
}
/*
	cmpl	$1, %edi        # compare  n with 1
	jle	.L20                # jump (l)ess than or (e)qual -> signed comparison
	movl	$1, %eax        # eax = 1
	movl	$2, %edx        # edx = 2
.L19:
	imull	%edx, %eax      # eax = eax * edx
	addl	$1, %edx        # edx = edx + 1
	cmpl	%edx, %edi      # compare n with i
	jge	.L19                # jump (g)reater or (e)qual
	rep ret                 # return eax
.L20:
	movl	$1, %eax
	ret
*/


int fact_for_goto(int n)
{
    int i = 2;
    int result = 1;
    if (!(i <= n))
        goto done;
loop:
    result *= i;
    ++i;
    if(i <= n) 
        goto loop;
done:
    return result;
}

/*
    cmpl	$1, %edi
	jle	.L25
	movl	$1, %eax
	movl	$2, %edx
.L24:
	imull	%edx, %eax
	addl	$1, %edx
	cmpl	%edx, %edi
	jge	.L24
	rep ret
.L25:
	movl	$1, %eax
.L23:
	ret
*/
	
int main() {

    int n;

    /* good until n = 16 */
    for (n = 1; n < 18; ++n) {
        printf("%d! = %d\n", n, fact_do(n));
    }

    /* good until n = 20 */
    for (n = 1; n < 22; ++n) {
        printf("%d! = %ld\n", n, fact_do2(n));
    }

    for(n = 1; n < 18; ++n) {
        printf("%d! = %d\n", n, fact_while(n));
    }

    for(n = 1; n < 18; ++n) {
        printf("%d! = %d\n", n, fact_while_goto(n));
    }

    return 0;
}
