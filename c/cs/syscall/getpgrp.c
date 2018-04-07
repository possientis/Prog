#include <stdio.h>
#include <unistd.h>

/*
 * using negative pid number in /bin/kill command
 * allows to send signal to every process in the 
 * group specified by that pid (the absolute value)
 * so process groups can be very useful and can
 * be set using setpgid system call function 
 */

int main() 
{
    pid_t p;

    p = getpid();
    printf("process id = %d\n", p);

    p = getpgrp();
    printf("process group id = %d\n", p);
    
    p = getppid();
    printf("parent process id = %d\n", p);

    return 0;
}


