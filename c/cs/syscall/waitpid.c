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
    pid_t pid;

    /* Parent creates N children */
    for(i = 0; i < N; ++i)
        if ((pid = Fork()) == 0) /* child */
            exit (100 + i);

    /* Parent reaps N children in no particuler order */
    while ((pid = waitpid(-1,&status,0)) > 0) {
        if(WIFEXITED(status))
            printf("child %d terminated normally with exit status %d\n",
                    pid, WEXITSTATUS(status));
        else
            printf("child %d terminated abnormally\n", pid);
    }

    /* The only normal termination is if there are no more children */
    if(errno != ECHILD)
        unix_error("waitpid error");

    exit(0);
}
