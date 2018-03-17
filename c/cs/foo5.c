#include <stdio.h>

void f(void);

int x = 15213;
int y = 15212;

int main() {

    x = 15213;
    f();
    printf("x = 0x%x y = 0x%x \n",x,y);
    return 0;
}
