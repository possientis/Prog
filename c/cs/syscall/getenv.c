#include <stdio.h>
#include <stdlib.h>

int main() {

    char *p;

    const char* NAME = "VIM";


    p = getenv(NAME);

    printf("%s = %s\n", NAME, p);

    return 0;
}
