#include <stdio.h>
#include "connect.h"

int main()
{

    int fd;

    fd = open_clientfd("localhost",80);

    printf("fd = %d\n", fd);

    return 0;
}
