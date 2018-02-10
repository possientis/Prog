#include <stdio.h>

int pushtest();
long poptest();

int main() 
{

    printf("pushtest() = %d\n", pushtest());
    printf("poptest() = 0x%lx\n", poptest());

    return 0;
}
