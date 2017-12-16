#include <stdio.h>

/* proof of correctness requires a precise semantics of '/' */
int umult_ok (unsigned x, unsigned y) {
    unsigned p = x * y;
    return !x || p/x == y;
}

int smult_ok (int x, int y) {
    int p = x * y;
    return !x || p/x == y;
}




int main() {
    unsigned two = 2U;
    unsigned x = 0x7FFFFFFFU;
    unsigned y = 0x4FFFFFFFU;
    unsigned z = 0xF1234567U;

    int mtwo = -2;
    int xx   = 0x7FFFFFFF;

    printf("umult_ok(x,two) = %d\n", umult_ok(x,two)); /* 1, is ok */
    printf("umult_ok(two,x) = %d\n", umult_ok(two,x)); /* 1, is ok */
    printf("umult_ok(y,two) = %d\n", umult_ok(y,two)); /* 1, is ok */
    printf("umult_ok(two,y) = %d\n", umult_ok(two,y)); /* 1, is ok */
    printf("umult_ok(z,two) = %d\n", umult_ok(z,two)); /* 0, is not ok */
    printf("umult_ok(two,z) = %d\n", umult_ok(two,z)); /* 0, is not ok */

    /* TODO */


    return 0;
}
