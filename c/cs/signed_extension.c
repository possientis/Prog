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

    /* Beware: converting from short signed int to unsigned int */
    unsigned uy = sx;  
    unsigned uz = (unsigned) (int) sx; /* C standard: uy = uz */
    unsigned ut = (unsigned) (unsigned short) sx;

    /* c7 cf ff ff on little endian machine */
    printf("uy = %u:\t", uy);
    show_bytes((byte_pointer) &uy, sizeof(unsigned));

    /* c7 cf ff ff on little endian machine */
    printf("uz = %u:\t", uz);
    show_bytes((byte_pointer) &uz, sizeof(unsigned));

    /* c7 cf 00 00 on little endian machine */
    printf("ut = %u:\t", ut);
    show_bytes((byte_pointer) &ut, sizeof(unsigned));


     

    return 0;
}

