#define _GNU_SOURCE
#include <string.h>
#include <signal.h>
#include <time.h>
#include "tlpi_hdr.h"

int
main(int argc, char *argv[])
{
  int sig;
  siginfo_t si;
  sigset_t allSigs;

  if (argc > 1 && strcmp(argv[1], "--help") == 0)
    usageErr("%s [delay-secs]\n", argv[0]);

  printf("%s: PID is %ld\n", argv[0], (long) getpid());

  /* Block all signals (except SIGKILL and SIGSTOP) */

  sigfillset(&allSigs);
  if (sigprocmask(SIG_SETMASK, &allSigs, NULL) == -1)
    errExit("sigprocmask");
  printf("%s: signals blocked\n", argv[0]);

  if (argc > 1) {     /* Delay so that signals can be sent to us */
    printf("%s: about to delay %s seconds\n", argv[0], argv[1]);
    sleep(getInt(argv[1], GN_GT_0, "delay-secs"));
    printf("%s: finished delay\n", argv[0]);
  }

  for (;;) {      /* Fetch signals until SIGINT (^C) or SIGTERM */
    sig = sigwaitinfo(&allSigs, &si);
    if (sig == -1)
      errExit("sigwaitinfo");

    if (sig == SIGINT || sig == SIGTERM)
      exit(EXIT_SUCCESS);

    printf("got signal: %d (%s)\n", sig, strsignal(sig));
    printf("    si_signo=%d, si_code=%d (%s), si_value=%d\n",
        si.si_signo, si.si_code,
        (si.si_code == SI_USER) ? "SI_USER" :
        (si.si_code == SI_QUEUE) ? "SI_QUEUE" : "other",
        si.si_value.sival_int);

    printf("    si_pid=%ld, si_uid=%ld\n",
        (long) si.si_pid, (long) si.si_uid);
  }
}




