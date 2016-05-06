#define USE_SIGSETJMP
#define _GNU_SOURCE             /* Get strsignal() declaration from <string.h> */
#include <string.h>
#include <setjmp.h>
#include <signal.h>
#include "signal_functions.h"   /* Declaration of printSigMask() */
#include "tlpi_hdr.h"


// 'volatile' prevents compiler from using a register for variable
// so variable is in memory. Don't really understand this yet.
// sig_atomic_t guarantees atomicity of write by signal and read by main prog
// ++ or -- are not atomic
static volatile sig_atomic_t canJump = 0;   /* Set to 1 once "env" buffer has been
                                             * initialized by [sig]setjmp() */
#ifdef USE_SIGSETJMP
static sigjmp_buf senv;
#else
static jmp_buf env;
#endif

static void
handler(int sig)
{
  /* UNSAFE: This handler uses non-async-signal-safe functions
   * (printf(), strsignal(), printSigMask(); see Section 21.1.2) */

  printf("Received signal %d (%s), signal mask is:\n", sig,
      strsignal(sig));
  printSigMask(stdout, NULL);

  if (!canJump) {
    printf("'env' buffer not yet set, doing a simple return\n");
    return;
  }

#ifdef USE_SIGSETJMP
  siglongjmp(senv, 1);
#else
  longjmp(env, 1);
#endif
}

int
main(int argc, char *argv[])
{
  struct sigaction sa;

  printSigMask(stdout, "Signal mask at startup:\n");

  sigemptyset(&sa.sa_mask);
  sa.sa_flags = 0;
  sa.sa_handler = handler;
  if (sigaction(SIGINT, &sa, NULL) == -1)
    errExit("sigaction");

#ifdef USE_SIGSETJMP
  printf("Calling sigsetjmp()\n");
  if (sigsetjmp(senv, 1) == 0)
#else
    printf("Calling setjmp()\n");
  if (setjmp(env) == 0)
#endif

    canJump = 1;          /* Executed after [sig]setjmp() */
  else
                          /* Executed after [sig]longjmp() */
    printSigMask(stdout, "After jump from handler, signal mask is:\n" );
  for (;;)
    pause();
}
