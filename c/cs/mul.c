#include <assert.h>
#include <stdio.h>

unsigned long mul1_fail (unsigned x, unsigned y) {
    /* 32 bits multiplication */
    return x*y;                                 /* movl  %edi, %eax             */
                                                /* imull %esi, %eax             */
}

unsigned long mul1(unsigned x, unsigned y) {
    return (unsigned long) x * (unsigned long) y;   /* movl %edi, &eax          */
                                                    /* movl %esi, %edi          */
                                                    /* imulq %rdi, %rax         */ 
}

unsigned long mul2 (unsigned long x, unsigned long y) {
    return x*y;                                 /* movq  %rdi, %rax             */
                                                /* imulq %rsi, %rax             */

}

unsigned long mul3 (unsigned short x, unsigned short y) {
    return x*y;                                 /* movzwl %di, %eax             */
                                                /* movzwl %si, %edi             */
                                                /* imull  %eax, %edi            */
                                                /* movslq %edi, %rax            */
}



int main() {
    printf("mul is running...\n");

    unsigned x1 = 0xFFFFFFFFU;
    unsigned y1 = 0xFFFFFFFFU;
    unsigned long z1 = mul1(x1,y1);

    printf("x1*y1 = 0x%.16lx\n", z1);


    return 0;
}

