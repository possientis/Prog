/* doesnt work as planned */

#define _XOPEN_SOURCE 500
#include <unistd.h>
#include <signal.h>
#include "tlpi_hdr.h"

static void
handler(int sig)
{
}

int
main(int argc, char *argv[])
{
  pid_t childPid;
  struct sigaction sa;

  setbuf(stdout, NULL);  /* Make stdout unbuffered */

  sigemptyset(&sa.sa_mask);
  sa.sa_flags = 0;
  sa.sa_handler = handler;
  if (sigaction(SIGHUP, &sa, NULL) == -1)
    errExit("sigaction");

  childPid = fork();
  if (childPid == -1)
    errExit("fork");

  if (childPid == 0 && argc > 1)  /* child */
    if (setpgid(0, 0) == -1)  /* Move to new process group */
      errExit("setpgid");

  printf("PID=%ld; PPID=%ld; PGID=%ld; SID=%ld\n", (long) getpid(),
      (long) getppid(), (long) getpgrp(), (long) getsid(0));

  alarm(10);  /* An unhandled SIGALRM ensures this process
               * will die if nothing else terminates it */

  for(;;) {  /* Wait for signals */
    pause();
    printf("%ld: caught SIGHUP\n", (long) getpid());
  }
}
