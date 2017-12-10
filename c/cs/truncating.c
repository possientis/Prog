#include <stdio.h>


int main() {
    int x = 53191;
    short sx = (short) x; 
    int y = sx;

    printf("x = %.8X,\t sx = %.4X,\t y = %.8X\n", x, sx, y);

    return 0;
}
