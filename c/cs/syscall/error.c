#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <unistd.h>


#include "error.h"

void unix_error(const char *msg)
{   
    fprintf(stderr, "%s: %s\n", msg, strerror(errno));
    exit(0);
} 

pid_t Fork(void)
{
    pid_t pid;

    if((pid = fork()) < 0)
        unix_error("Fork error");

    return pid;
}

char* Fgets(char* s, int size, FILE * stream) {

    char* out;
    
    out = fgets(s,size,stream);

    if (out == NULL) {
        if (!feof(stream)) {
            unix_error("Fgets error");
        }
    }

    return out;
}



