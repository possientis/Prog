#include <stdio.h>
#include <stdlib.h>  /* exit */
#include <unistd.h>  /* fork */
#include <signal.h>  /* kill */

int main()
{
    pid_t pid;
    int k;

    /* child sleeps until SIGKILL signal is received then dies */
    if ((pid = fork()) == 0) {
        printf("child is going to sleep\n");
        pause();    /* wait for signal to arrive */
        printf("control should never reach this point\n");
        exit(0);
    }

    sleep(1);

    printf("parent process sending SIGKILL signal now\n");

    if((k = kill(pid,SIGKILL)) != 0)
        printf("signal was not successfully sent, error = %d\n",k);
    else
        printf("signal was successfully sent\n");

    exit(0);
}
