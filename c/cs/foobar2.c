#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/wait.h>



int main ()
{
    int fd;
    char c;

    /* the two file descriptors (in parent descriptor table and 
     * in child descriptor table) point to the same file table
     * entry. Hence a single file position.
     */
    fd = open("foobar.txt", O_RDONLY, 0);
    if(fork() == 0) {
        read(fd, &c, 1);
        exit(0);
    }

    wait(NULL);

    read(fd, &c, 1);

    printf("c = %c\n", c); /* c = o */
    exit(0);
}
