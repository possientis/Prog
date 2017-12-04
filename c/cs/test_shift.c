#include <stdio.h>



int main() {

    int x       = 0xFFFFFFC3;
    unsigned ux = 0xFFFFFFC3;

    int y       = 0x7FFFFFC3;
    unsigned uy = 0x7FFFFFC3;

    printf("x >> 2 = %.8X,\tux >> 2 = %.8X\n", x >> 2, ux >> 2); 
    printf("y >> 2 = %.8X,\tuy >> 2 = %.8X\n", y >> 2, uy >> 2); 

    return 0;
}
