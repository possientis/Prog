#include <stdio.h>


int fun1 (unsigned word) {
    return (int) ((word << 24) >> 24);
} 

int fun2 (unsigned word) {
    return ((int) word << 24) >> 24;
}

int main() {

    unsigned x = 0x00000076U;
    unsigned y = 0x87654321U;
    unsigned z = 0x000000C9U;
    unsigned t = 0xEDCBA987U;

    /* right shift on unsigned is logical: 0x00000076 */
    printf("x = 0x%.8X,\t fun1(x) = 0x%.8X\n", x, fun1(x));


    /* right shift on unsigned is logical: 0x00000021 */
    printf("y = 0x%.8X,\t fun1(y) = 0x%.8X\n", y, fun1(y));

    /* right shift on unsigned is logical: 0x000000C9 */
    printf("z = 0x%.8X,\t fun1(z) = 0x%.8X\n", z, fun1(z));

    /* right shift on unsigned is logical: 0x00000087 */
    printf("t = 0x%.8X,\t fun1(t) = 0x%.8X\n", t, fun1(t));

    /* right shift on signed is arithmetical and leading 
     * bit is 0 =>  0x00000076 */
    printf("x = 0x%.8X,\t fun2(x) = 0x%.8X\n", x, fun2(x));

    /* right shift on signed is arithmetical and leading 
     * bit is 0 =>  0x00000021 */
    printf("y = 0x%.8X,\t fun2(y) = 0x%.8X\n", y, fun2(y));

    /* right shift on signed is arithmetical and leading 
     * bit is 1 =>  0xFFFFFFC9 */
    printf("z = 0x%.8X,\t fun2(z) = 0x%.8X\n", z, fun2(z));

    /* right shift on signed is arithmetical and leading 
     * bit is 1 =>  0xFFFFFF87 */
    printf("t = 0x%.8X,\t fun2(t) = 0x%.8X\n", t, fun2(t));

    return 0;
}
