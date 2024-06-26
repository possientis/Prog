// COMPUTER CRASHED ON THIS EXAMPLE
//
#define _GNU_SOURCE   /* Get strsignal() declaration from <string.h> */
#include <string.h>
#include <signal.h>
#include "tlpi_hdr.h"

static void
sigsegvHandler(int sig)
{
  int x;

  /* UNSAFE: This handler uses non-async-signal-safe functions
   * (printf(), strsignal(), fflush(); see Section 21.1.2) */

  printf("Caught signal %d (%s)\n", sig, strsignal(sig));
  printf("Top of handler stack near %10p\n", (void *) &x);
  fflush(NULL);

  _exit(EXIT_FAILURE);    /* Can't return after SIGSEGV */
}

static void       /* A recursive function that overflows the stack */
overflowStack(int callNum)
{
  char a[100000];   /* Make this stack frame large */
  printf("Call %4d - top of stack near %10p\n", callNum, &a[0]);
  overflowStack(callNum+1);
}


int
main(int argc, char *argv[])
{
  stack_t sigstack;
  struct sigaction sa;
  int j;

  printf("Top of standard stack is near %10p\n", (void *) &j);

  /* Allocate alternate stack and inform kernel of its existence */

  sigstack.ss_sp = malloc(SIGSTKSZ);
  if (sigstack.ss_sp == NULL)
    errExit("malloc");

  sigstack.ss_size = SIGSTKSZ;
  sigstack.ss_flags = 0;
  if (sigaltstack(&sigstack, NULL) == -1)
    errExit("sigaltstack");
  printf("Alternate stack is at %10p-%p\n",
      sigstack.ss_sp, (char *) sbrk(0) - 1);

  sa.sa_handler = sigsegvHandler; /* Establish handler for SIGSEGV */
  sigemptyset(&sa.sa_mask);
  sa.sa_flags = SA_ONSTACK;       /* Handler uses alternate stack */
  if (sigaction(SIGSEGV, &sa, NULL) == -1)
    errExit("sigaction");

  overflowStack(1);
}

