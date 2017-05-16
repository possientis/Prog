#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
/* Some labeled signal defines from signal.h
 * #define SIGHUP     1 Hangup
 * #define SIGINT     2 Interrupt (Ctrl-C)
 * #define SIGQUIT    3 Quit (Ctrl-\)
 * #define SIGILL     4 Illegal instruction
 * #define SIGTRAP    5 Trace/breakpoint trap
 * #define SIGABRT    6 Process aborted
 * #define SIGBUS     7 Bus error
 * #define SIGFPE     8 Floating point error
 * #define SIGKILL    9 Kill
 * #define SIGUSR1    10 User defined signal 1
 * #define SIGSEGV    11 Segmentation fault
 * #define SIGUSR2    12 User defined signal 2
 * #define SIGPIPE    13 Write to pipe with no one reading
 * #define SIGALRM    14 Countdown alarm set by alarm()
 * #define SIGTERM    15 Termination (sent by kill command)
 * #define SIGCHLD    17 Child process signal
 * #define SIGCONT    18 Continue if stopped
 * #define SIGSTOP    19 Stop (pause execution)
 * #define SIGTSTP    20 Terminal stop [suspend] (Ctrl-Z)
 * #define SIGTTIN    21 Background process trying to read stdin
 * #define SIGTTOU    22 Background process trying to read stdout
 */

/* A signal handler */
void signal_handler(int signal) {
  printf("Caught signal %d\t", signal);
  if (signal == SIGTSTP)
    printf("SIGTSTP (Ctrl-Z)");
  else if (signal == SIGQUIT)
    printf("SIGQUIT (Ctrl-\\)");
  else if (signal == SIGUSR1)
    printf("SIGUSR1");
  else if (signal == SIGUSR2)
    printf("SIGUSR2");
  printf("\n");
}

void sigint_handler(int x) {
  printf("Caught a Ctrl-C (SIGINT) in a separate handler\nExiting.\n");
  exit(0);
}

int main() {
  /* Registering signal handlers */
  signal(SIGQUIT, signal_handler); // Set signal_handler() as the
  signal(SIGTSTP, signal_handler); // signal handler for these
  signal(SIGUSR1, signal_handler); // signals.
  signal(SIGUSR2, signal_handler);
  signal(SIGINT,  sigint_handler); // Set sigint_handler() for SIGINT.
  while(1) {}  // Loop forever.
}
