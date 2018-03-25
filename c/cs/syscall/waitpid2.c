#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/wait.h>
#include <errno.h>

#include "error.h"

#define N 10


int main()
{
    int status, i;
    pid_t pid[N], retpid;

    /* Parent creates N children */
    for(i = 0; i < N; ++i)
        if((pid[i] = Fork()) == 0) /* child */
            exit (100 + i);

    i = 0;
    /* Parent reaps N children in order */
    while ((retpid = waitpid(pid[i++], &status, 0)) > 0) {
        if(WIFEXITED(status))
            printf("child %d terminated normally with exit status=%d\n",
                    retpid, WEXITSTATUS(status));
        else
            printf("child %d terminated abnormally\n", retpid);
    }

    /* the only normal termination is if there are no more children */
    if(errno != ECHILD) 
        unix_error("waitpid error");


    exit(0);
}


