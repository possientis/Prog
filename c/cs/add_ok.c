#include <stdio.h>

/* returns 1 if two unsigned arguments can be added without carry */
int uadd_ok(unsigned x, unsigned y) {
    return x < x + y;
}

/* returns 1 if two signed arguments can be added without overflow */
int sadd_ok(int x, int y) {
    int b1 = ((x >= 0) && (y >=0) && (x + y < 0));
    int b2 = ((x < 0)  && (y < 0) && (x + y >= 0));
    return !(b1 || b2);
}

/* Warning: this code is buggy */
int sadd_ok2(int x, int y) {
    int sum = x + y;

    /* always returns 1, as modulo arithmetics never fails */
    return (sum - x == y) && (sum - y == x);

}

int main() {

    unsigned x = 0xFFFFFFFF;
    unsigned y = 0xFFFFFFFE;
    unsigned z = 0x00000001;

    printf("uadd_ok(x,z) = %d\n", uadd_ok(x,z)); /* 0, not ok, overflow */
    printf("uadd_ok(y,z) = %d\n", uadd_ok(y,z)); /* 1, is ok, no overflow */ 

    int sx = 0x7FFFFFFF;
    int sy = 0x7FFFFFFE;
    int sz = 0x00000001;
    int sa = -0x80000000;
    int sb = -0x7FFFFFFF;
    int sc = -0x00000001;

    printf("sadd_ok(sx,sz) = %d\n", sadd_ok(sx,sz)); /* 0, not ok, overflow */
    printf("sadd_ok(sy,sz) = %d\n", sadd_ok(sy,sz)); /* 1, is ok, no overflow */
    printf("sadd_ok(sa,sc) = %d\n", sadd_ok(sa,sc)); /* 0, not ok, overflow */
    printf("sadd_ok(sb,sc) = %d\n", sadd_ok(sb,sc)); /* 1, is ok, no overflow */
    printf("sadd_ok(sx,sa) = %d\n", sadd_ok(sx,sa)); /* 1, is ok, no overflow */
    printf("sadd_ok(sx,sb) = %d\n", sadd_ok(sx,sb)); /* 1, is ok, no overflow */
    printf("sadd_ok(sx,sc) = %d\n", sadd_ok(sx,sb)); /* 1, is ok, no overflow */
    printf("sadd_ok(sy,sa) = %d\n", sadd_ok(sy,sa)); /* 1, is ok, no overflow */
    printf("sadd_ok(sy,sb) = %d\n", sadd_ok(sy,sb)); /* 1, is ok, no overflow */
    printf("sadd_ok(sy,sc) = %d\n", sadd_ok(sy,sc)); /* 1, is ok, no overflow */
    printf("sadd_ok(sz,sa) = %d\n", sadd_ok(sz,sa)); /* 1, is ok, no overflow */
    printf("sadd_ok(sz,sb) = %d\n", sadd_ok(sz,sb)); /* 1, is ok, no overflow */
    printf("sadd_ok(sz,sc) = %d\n", sadd_ok(sz,sc)); /* 1, is ok, no overflow */

    printf("sadd_ok2(sx,sz) = %d\n", sadd_ok2(sx,sz)); /* BUG 1 */
    printf("sadd_ok2(sy,sz) = %d\n", sadd_ok2(sy,sz)); /* 1, is ok, no overflow */
    printf("sadd_ok2(sa,sc) = %d\n", sadd_ok2(sa,sc)); /* BUG 1 */
    printf("sadd_ok2(sb,sc) = %d\n", sadd_ok2(sb,sc)); /* 1, is ok, no overflow */
    printf("sadd_ok2(sx,sa) = %d\n", sadd_ok2(sx,sa)); /* 1, is ok, no overflow */
    printf("sadd_ok2(sx,sb) = %d\n", sadd_ok2(sx,sb)); /* 1, is ok, no overflow */
    printf("sadd_ok2(sx,sc) = %d\n", sadd_ok2(sx,sb)); /* 1, is ok, no overflow */
    printf("sadd_ok2(sy,sa) = %d\n", sadd_ok2(sy,sa)); /* 1, is ok, no overflow */
    printf("sadd_ok2(sy,sb) = %d\n", sadd_ok2(sy,sb)); /* 1, is ok, no overflow */
    printf("sadd_ok2(sy,sc) = %d\n", sadd_ok2(sy,sc)); /* 1, is ok, no overflow */
    printf("sadd_ok2(sz,sa) = %d\n", sadd_ok2(sz,sa)); /* 1, is ok, no overflow */
    printf("sadd_ok2(sz,sb) = %d\n", sadd_ok2(sz,sb)); /* 1, is ok, no overflow */
    printf("sadd_ok2(sz,sc) = %d\n", sadd_ok2(sz,sc)); /* 1, is ok, no overflow */



    return 0;
}


