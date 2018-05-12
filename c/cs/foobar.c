#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>


int main ()
{
    int fd1;
    int fd2;

    char c;
    
    /* the two file descriptors of descriptor table 
     * point to two different entries in the file table,
     * and these two file table entries point to the same
     * v-node in v-node table. These two entries have
     * separate file positions
     */
    fd1 = open("foobar.txt",O_RDONLY,0);
    fd2 = open("foobar.txt",O_RDONLY,0);
    read(fd1, &c, 1);
    read(fd2, &c, 1);   /* reading 'f' twice */

    printf("c = %c\n",c); /* c = f */
    exit(0);
}
