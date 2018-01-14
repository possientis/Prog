#include <stdio.h>

#define OP /


int arith(int x) {
    return x OP 4;
}

/* we want :
 *
 * leal 3(%rdi), %eax
 * testl %edi, %edi
 * cmovns %edi, %eax
 * sarl $2, %eax
 */



int main () {
    int x = -7;

    printf("-7/4 = %d\n", (x+3) >> 2);

    return 0;
}
