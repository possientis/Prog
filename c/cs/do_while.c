#include <stdio.h>


void loop1() {
    int x = 5;

    do 
        printf("x = %d\n", x--);
    while (x >= 0);

}


void loop2() {
    int x = 5;

loop:
    printf("x = %d\n", x--);
    if (x >= 0)
        goto loop;

}


int main () {

    loop1();
    printf("========================\n");
    loop2();

    return 0;
}


int dw_loop(int x, int y, int n) {

    do {
        x += n;
        y *= n;
        n--;
    } while ((n > 0) && (y < n));

    return x;
}
/*
	movl	%edi, %eax      # eax = x
.L12:
	addl	%edx, %eax      # x = x + n
	imull	%edx, %esi      # y = y * n
	subl	$1, %edx        # n = n - 1;
	testl	%edx, %edx      # and n ?
	jle	.L14                # jump (l)ess-or-(e)qual -> signed comparison
	cmpl	%edx, %esi      # compare y with n (care order: cmpl n, y)
	jl	.L12                # jump (l)ess -> signed comparison
.L14:
	rep ret
*/



