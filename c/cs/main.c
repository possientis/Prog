#include <stdio.h>
#include <string.h>

#include "show_bytes.h"



int main() {

    short x = 12345;
    short y = -x;

    show_bytes((byte_pointer) &x, sizeof(short));
    show_bytes((byte_pointer) &y, sizeof(short));


    return 0;
}
