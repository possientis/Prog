#include <stdio.h>

#include "logical.h"

int main() {
    int x = 0x66;
    int y = 0x39;
    printf("x = 0x%.2X\t y = 0x%.2X\n", x, y);
    printf("x & y = 0x%.2X\t x && y = 0x%.2X\n", x & y, x && y);
    printf("x | y = 0x%.2X\t x || y = 0x%.2X\n", x | y, x || y);
    printf("~x | ~y = 0x%.2X\t !x || !y = 0x%.2X\n", ~x | ~y, !x || !y);
    printf("x & !y = 0x%.2X\t x && ~y = 0x%.2X\n", x & !y, x && ~y);
    printf("equals(x,y) = %d\n",equals(x,y));
    printf("equals(y,x) = %d\n",equals(y,x));
    printf("equals(x,x) = %d\n",equals(x,x));
    printf("equals(y,y) = %d\n",equals(y,y));


    return 0;
}
