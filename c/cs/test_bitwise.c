#include <stdio.h>

#include "bitwise.h"


int main() {

    int x = 0x87654321;
    int y = 0xF0F0F0F0;

    printf("least significant byte: 0x%.8X\n",least_byte(x));
    printf("complement all but least: 0x%.8X\n",complement_all_but_least(x));
    printf("least set to one: 0x%.8X\n",least_set_to_one(x));
    printf("after setting : 0x%.8X\n", bis(x,y));
    printf("after clearing : 0x%.8X\n", bic(x,y));
    printf("checking bool_or : 0x%.8X\n", bool_or(x,y));
    printf("checking bool_xor : 0x%.8X\n", bool_xor(x,x));
    printf("checking bool_xor : 0x%.8X\n", bool_xor(y,bool_xor(y,x)));
    return 0;
}
