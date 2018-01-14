#include <stdio.h>

void loop1() {
    int x = 5;

    while (x >= 0)
        printf("x = %d\n", x--);
}


int main() {

    loop1();

    return 0;
}
