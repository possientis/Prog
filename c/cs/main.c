#include <string.h>

#include "show_bytes.h"



int main() {

    const char *s = "abcdef";
    show_bytes((byte_pointer) s, strlen(s)); /* 61 62 63 64 65 66 */
    return 0;
}
