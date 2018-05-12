#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>

int main(int argc, char *argv[])
{
    struct stat stat1;
    char *type, *readok;

    stat(argv[1], &stat1);
    if(S_ISREG(stat1.st_mode))
        type = "regular";
    else if (S_ISDIR(stat1.st_mode))
        type = "directory";
    else
        type = "other";

    if((stat1.st_mode & S_IRUSR))    /* check read access */
        readok = "yes";
    else
        readok = "no";

    printf("type: %s, read: %s\n", type, readok);

    exit(0);
}
