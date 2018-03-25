#include <stdio.h>
#include <unistd.h>


int main()
{

    int i, sec = 5;

    printf("sleeping for %d seconds\n", sec);
    i = sleep(sec);
    printf("return value is %d\n", i);

    return 0;
}
