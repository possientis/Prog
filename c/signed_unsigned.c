#include <stdio.h>

/* compile with -Wsign-compare option */

int main() {

    int x = 34;
    unsigned y = 46;

    return (x <= y);
}
