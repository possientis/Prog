#include <stdio.h>
#include <stdlib.h>  /* exit */
#include <signal.h>  /* signal */
#include <unistd.h>  /* alarm */

void handler(int sig)
{
    static int beeps = 0;

    printf("BEEP\n");
    if(++beeps < 5)
        alarm(1);   /* kernel will send SIGALRM to process in 1 sec */
    else
    {
        printf("BOOM!\n");
        exit(0);
    }
}

int main()
{

    signal(SIGALRM,handler); /* install SIGALRM handler */
    alarm(1);                 /* next alarm in 1 second  */


    while(1) {
        ;   /* signal handler returns control here each time */
    }

    printf("control should never reach this point\n");
    exit(0);
}
