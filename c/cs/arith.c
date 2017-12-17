#include <stdio.h>

/* if x <= 0, we would expect x - 1 < 0. However, this may 
 * not be the case because of overflow  */

int A(int x) {
    return (x > 0) || (x - 1 < 0);
}

/* the condition (x & 7) != 7 fails if bit 0 1 2 are all set.
 * In that case, bit 2 is set and consequently bit 31 of (x << 29)
 * is set and (x << 29 < 0) should return 1 */

int B(int x) {
    return (x & 7) != 7 || (x << 29 < 0);
}


/*  One would think that x * x >= always holds, but it may
 *  fail due to overflow */

int C(int x) {
    return (x * x) >= 0;
}

int main () {

    int xa = -0x80000000;
    printf("A(xa) = %d\n", A(xa)); /* A(xa) = 0 */ 

    int xb;
    for(xb = 0; xb < 16; ++xb) {
        printf("B(xb) = %d\n", B(xb));
    }

    int xc = 0xC000;
    printf("C(xc) = %d\n", C(xc)); /* C(xc) = 0 */

    /* TODO */

    return 0;
}
