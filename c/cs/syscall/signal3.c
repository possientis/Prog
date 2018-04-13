#include <stdio.h>
#include <stdlib.h>     /* exit */
#include <sys/wait.h>   /* waitpid */
#include <signal.h>     /* signal */
#include <unistd.h>     /* read */
#include <errno.h>      /* errno */

#include "Signal.h"

#define MAXBUF 8192



void handler(int sig)
{
  pid_t pid;

  while ((pid = waitpid(-1, NULL, 0)) > 0)
    printf("Handler reaped child %d\n", (int) pid);

  if(errno != ECHILD)
    fprintf(stderr,"waitpid error\n");

  sleep(2);
  return;
}


int main()
{
  int i, n;
  char buf[MAXBUF];
  pid_t pid;

  /* semantics of 'signal' varies from system to system
   * hence signal is not portable and should not be used. 
   * For example, the question
   * of whether a slow system call (i.e. which blocks like read)
   * gets restarted after a signal handler has run or whether
   * it returns with the errno EINTR, is not uniform across
   * systems. (it does get restarted on linux)
   */
  if(Signal(SIGCHLD, handler) == SIG_ERR){
    fprintf(stderr,"Failed to install SIGCHLD handler\n");
    exit(-1);
  }

  /* parent creates children */
  for(i = 0; i < 3; ++i) {
    if((pid = fork()) == -1) {
      fprintf(stderr, "Failed to fork\n");
      exit(-1);
    }
    if(pid == 0) {
      printf("Hello from child %d\n", (int) getpid());
      sleep(1);
      exit(0);
    }
  }


  /* parent waits for terminal input and then processes it */
  if((n = read(STDIN_FILENO, buf, sizeof(buf))) < 0) {
    fprintf(stderr, "read error\n");
    exit(-1);
  }

  printf("Parent processing input\n");
  while(1);

  printf("Control flow should not reach this point\n");
  exit(0);
}
       
