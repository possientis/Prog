#include <stdio.h>




struct P1 {int i; char c; long j; char d; };    /* 24 bytes (why not 20?)*/
struct P2 {int i; char c; char d; long j; };    /* 16 bytes */
struct P3 {long j; char c; char d; int i; };    /* 16 bytes */
struct P4 {short w[3]; char c[3];};             /* 10 bytes */


int main() {

    printf("sizeof(struct P1) = %d\n", sizeof(struct P1));
    printf("sizeof(struct P2) = %d\n", sizeof(struct P2));
    printf("sizeof(struct P3) = %d\n", sizeof(struct P3));
    printf("sizeof(struct P4) = %d\n", sizeof(struct P4));

    struct P1 p1;
    int offset_c = (void*) &p1.c - (void*) &p1.i;
    int offset_j = (void*) &p1.j - (void*) &p1.i;
    int offset_d = (void*) &p1.d - (void*) &p1.i;


    printf("offset_c = %d\n", offset_c);
    printf("offset_j = %d\n", offset_j);
    printf("offset_d = %d\n", offset_d);

    return 0;
}


