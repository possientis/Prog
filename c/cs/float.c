#include <stdio.h>
#include <assert.h>

/* The conversion from int to double will not overflow 
 * and will not yield a loss of precision. So the conversion
 * should be exact. The conversion from double to int should
 * give us back the original int. Should always return 1.
 */

int A(int x) {
    return x == (int) (double) x;
}

/* The conversion from int to float cannot overflow. However,
 * it can be rounded. Hence it possible for this to return 0
 */

int B(int x) {
    return x == (int) (float) x;
}


/* The conversion from double to float reduces range and precision,
 * hence both overflow and rounding may occur. So this will return 0
 * in some cases 
 */

int C(double d) {
    return d == (double) (float) d;
}


/* should return 1 */
int D(float f) {
    return f == (float) (double) f;
}

/* minus operator only switches the sign bit: there is
 * no rounding and no overflow ever. This should return 1.
 */

int E(float f) {
    return f == -(-f);
}

/* surely, this has got to be 1 */
int F() {
    return 1.0/2 == 1/2.0;
}


/* floating representations always works well with 
 * comparisons, unlike signed and unsigned comparisons
 * which may be conter-intuitive due to overflow.
 * This should return 1
 */

int G(double d) {
    return d * d >= 0;
}


/* see counter-example */
int H(float f, double d) {
    return (f + d) - f == d;
}

int main() {

    unsigned long count = 0;
    int x;

    for(x = -0x80000000; x < 0x7fff0000; x += 43) {
        assert (A(x) == 1);
        count += 1;
    }

    int xb = 0x8000002b;
    printf("B(xb) = %d\n", B(xb)); /* B(xb) = 0 */
    printf("xb = 0x%x\n",xb);                           /* 0x8000002b as Hex  */
    printf("xb = %d\n", xb);                            /* -2147483605 as Dec */
    printf("(float) xb = %f\n", (float) xb);            /* -2147483648.0      */
    printf("(int) (float) xb = %d\n", (int) (float) xb); /* 2147483648        */ 

    double d = 1.0e25;
    printf("C(d) = %d\n", C(d)); /* C(d) = 0 */

    float f;
    for(f = -2.0e9; f < 2.0e9; f+=1.0e2) {
        assert(D(f) == 1);
        count += 1;
    }

    for(f = -2.0e9; f < 2.0e9; f+=1.0e2) {
        assert(E(f) == 1);
        count += 1;
    }

    assert (F() == 1);

    for(d = -2.0e270; d < 2.0e270; d+=1.0e263) {
        assert(G(d) == 1);
        count += 1;
    }

    d = 1.0;
    f = 1.0e20;
    printf("H(f,d) = %d\n", H(f,d)); /* H(f,d) = 0 */


    printf("Number of checks carried out: 0x%lx\n",count);

    return 0;
}
