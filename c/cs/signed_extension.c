#include <stdio.h>

#include "show_bytes.h"

int main() {

    short sx = -12345;          /* -12345 */
    unsigned short usx = sx;    /* 53191  */

    int x = sx;                 /* -12345 */
    unsigned ux = usx;          /* 53191  */


    printf("sx = %d:\t", sx);
    show_bytes((byte_pointer) &sx, sizeof(short));

    printf("usx = %u:\t", usx);
    show_bytes((byte_pointer) &sx, sizeof(short));

    printf("x = %d:\t", x);
    show_bytes((byte_pointer) &x, sizeof(int));

    printf("ux = %u:\t", ux);
    show_bytes((byte_pointer) &ux, sizeof(unsigned));

    return 0;
}

