#include <stdio.h>
#include <sys/types.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/wait.h>
#include <assert.h>

int main() {

    pid_t p,q;
    p = fork();

    int x = 23;

    if(p == 0) {
        printf("I am the child process with pid = %d\n", getpid());

        /* will get unexpected result if you let parent terminate 
         * before this line is executed.                          */
        printf("My parent process has pid = %d\n", getppid());
        x--;
        printf("As a child, x = %d\n", x);
        exit(23);
    }
    else {
        printf("I am the parent process with pid = %d\n", getpid());
        printf("My child process has pid = %d\n", p);
        x++;
        printf("As a parent, x = %d\n", x); 
        int status;
        int option = 0;
        /* will block until child terminates. will reap child zombie */
        q = waitpid(p, &status, option);  
        printf("My child terminated with status = %d\n", WEXITSTATUS(status));
        assert (p == q);
    }

    return 0;
}

