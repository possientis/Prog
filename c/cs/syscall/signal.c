#include <stdio.h>
#include <stdlib.h>   /* exit */
#include <unistd.h>   /* pause */
#include <signal.h>


void handler(int sig) /* SIGINT handler */
{
  printf("Caught SIGINT\n");
  exit(0);
}

int main()
{
  /* install the SIGINT handler */
  if(signal(SIGINT,handler) == SIG_ERR){
    fprintf(stderr,"Failed to install SIGINT handler\n");
    exit(-1);
  }

  pause();  /* wait for receipt of signal */

  exit(0);
}
