#include <stdio.h>
#include <assert.h>

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


/* If q = 2^32, the binary representation of x is either
 * in [q/2,q[ (in which case x < 0 is true) or in 
 * [0,q/2[ (in which case -x does not overflow and
 * -x <= 0 is true. should return 1 */
int D(int x) {
    return x < 0 || -x <= 0;
}

/* If q = 2^32 and the binary representation of x is
 * q/2, then x > 0 fails. However, -x overflows and
 * yields x. So -x >= 0 also fails */

int E(int x) {
    return x > 0 || -x >= 0;
}

/* conversion from signed to unsigned does not change
 * binary representation. If q = 2^32, then both signed
 * and unsigned addition are simply addition modulo q,
 * so x + y and ux + uy have the same binary representation.
 * The binary comparision triggers a conversion of x + y
 * to an unsigned number which does not change binary 
 * representation. So this should always return 1. */

int F(int x, int y) {
    unsigned ux = x;
    unsigned uy = y;
    return x + y == ux + uy;
}

/* If q = 2^32, then x and ux have the same binary
 * representation. They are the same number modulo q.
 * Likewise, y and uy are the same number modulo q.
 * addition, multiplication and - are exact operation
 * modulo q. The ~y operator satisfies the equality
 * y + ~y = q - 1 modulo q, and consequently 
 * ~y = -y - 1 modulo q. Hence we are effectively
 * testing the equality modulo q:
 * x * (-y - 1) + x * y = - x which is true.
 * Should always return 1 */

int G(int x, int y) {
    unsigned ux = x;
    unsigned uy = y;
    return x*~y + uy*ux == -x;
}


int main () {

    int xa = -0x80000000;
    printf("A(xa) = %d\n", A(xa)); /* A(xa) = 0 */ 

    int xb;
    for(xb = 0; xb < 16; ++xb) {
        assert (B(xb) == 1);
    }

    int xc = 0xC000;
    printf("C(xc) = %d\n", C(xc)); /* C(xc) = 0 */

    int xd = 0x80000000;
    int i;
    for(i = -8; i < 9; ++i) {
        assert(D(xd + i) == 1);
    }

    int xe = 0x80000000;
    printf("E(xe) = %d\n", E(xe)); /* E(xe) = 0 */

    int xf = 0x7FFFFFFF;
    int yf;
    for (yf = -8; yf < 9; ++yf) {
        assert (F(xf,yf) == 1);
    }

    int xg = 0x7FFFFFFF;
    int yg;
    for (yg = -8; yg < 9; ++yg) {
        assert (G(xg,yg) == 1);
    }

    return 0;
}
