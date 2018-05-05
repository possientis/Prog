#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>

ssize_t readchar(char* pc)
{
    ssize_t n;
    printf("\nabout to read one character\n");
    n = read(STDIN_FILENO, pc, 1);
    printf("\ndone reading one character\n");
    return n;
}

int main ()
{

    char c;

    while (readchar(&c) != 0) {
        printf("\nabout to write\n");
        write(STDOUT_FILENO, &c,1);
        printf("\nwrote one character\n");
    }

    exit(0);
}





