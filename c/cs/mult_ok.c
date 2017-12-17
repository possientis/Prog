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

int umult_ok2 (unsigned x, unsigned y) {
    /* unsigned long p = x * y; ---> BUG !!! */
    unsigned long p = (unsigned long) x * (unsigned long) y;
    return p <= 0xFFFFFFFFUL;
}

int smult_ok2 (int x, int y) {
    long p = (long) x * (long) y;
    return (p <= 0x7FFFFFFFL) && (p >= -0x80000000L);
}



int main() {
    unsigned two = 2U;
    unsigned x = 0x7FFFFFFFU;
    unsigned y = 0x4FFFFFFFU;
    unsigned z = 0xF1234567U;

    int mtwo = -2;
    int stwo = 2;

    int sx   = 0x3FFFFFFF;
    int sy   = 0x40000000;

    printf("unsigned:\n");
    printf("umult_ok(x,two) = %d\n", umult_ok(x,two)); /* 1, is ok */
    printf("umult_ok(two,x) = %d\n", umult_ok(two,x)); /* 1, is ok */
    printf("umult_ok(y,two) = %d\n", umult_ok(y,two)); /* 1, is ok */
    printf("umult_ok(two,y) = %d\n", umult_ok(two,y)); /* 1, is ok */
    printf("umult_ok(z,two) = %d\n", umult_ok(z,two)); /* 0, is not ok */
    printf("umult_ok(two,z) = %d\n", umult_ok(two,z)); /* 0, is not ok */
    printf("umult_ok2(x,two) = %d\n", umult_ok2(x,two)); /* 1, is ok */
    printf("umult_ok2(two,x) = %d\n", umult_ok2(two,x)); /* 1, is ok */
    printf("umult_ok2(y,two) = %d\n", umult_ok2(y,two)); /* 1, is ok */
    printf("umult_ok2(two,y) = %d\n", umult_ok2(two,y)); /* 1, is ok */
    printf("umult_ok2(z,two) = %d\n", umult_ok2(z,two)); /* 0, is not ok */
    printf("umult_ok2(two,z) = %d\n", umult_ok2(two,z)); /* 0, is not ok */


    printf("signed:\n");
    printf("smult_ok(sx,mtwo) = %d\n", smult_ok(sx,mtwo)); /* 1, is ok */
    printf("smult_ok(mtwo,sx) = %d\n", smult_ok(mtwo,sx)); /* 1, is ok */
    printf("smult_ok(sx,stwo) = %d\n", smult_ok(sx,stwo)); /* 1, is ok */
    printf("smult_ok(stwo,sx) = %d\n", smult_ok(stwo,sx)); /* 1, is ok */
    printf("smult_ok(sy,mtwo) = %d\n", smult_ok(sy,mtwo)); /* 1, is ok */
    printf("smult_ok(mtwo,sy) = %d\n", smult_ok(mtwo,sy)); /* 1, is ok */
    printf("smult_ok(sy,stwo) = %d\n", smult_ok(sy,stwo)); /* 0, is not ok */
    printf("smult_ok(stwo,sy) = %d\n", smult_ok(stwo,sy)); /* 0, is not ok */
    printf("smult_ok2(sx,mtwo) = %d\n", smult_ok2(sx,mtwo)); /* 1, is ok */
    printf("smult_ok2(sx,stwo) = %d\n", smult_ok2(sx,stwo)); /* 1, is ok */
    printf("smult_ok2(sy,mtwo) = %d\n", smult_ok2(sy,mtwo)); /* 1, is ok */
    printf("smult_ok2(sy,stwo) = %d\n", smult_ok2(sy,stwo)); /* 0, is not ok */


    return 0;
}
