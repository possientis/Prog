#include <stdio.h>

/* gcc -c baz.c; ar rcs baz.a baz.o         # static */
/* gcc -shared -fPIC -o baz.so  baz.c       # shared */

void baz()
{
    printf("hello world!\n");
}
