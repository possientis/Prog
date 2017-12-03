#include <stdio.h>
#include <string.h>

#include "inplace_swap.h"
#include "show_bytes.h"



int main() {
    int a = 43;
    int b = 36;
    int c[4] = {1,2,3,4};
    int d[5] = {1,2,3,4,5};

    printf("Before swap:\t a = %d, b= %d\n", a, b);
    inplace_swap(&a,&b);
    printf("After swap:\t a = %d, b= %d\n", a, b);
    printf("============\n");
    printf("Before reverse:\t c = "); show_bytes((byte_pointer) &c, 16);
    printf("Before reverse:\t d = "); show_bytes((byte_pointer) &d, 20);
    reverse_array(c,4); reverse_array(d,5);
    printf("After reverse:\t c = "); show_bytes((byte_pointer) &c, 16);
    printf("After reverse:\t d = "); show_bytes((byte_pointer) &d, 20);




    return 0;
}
