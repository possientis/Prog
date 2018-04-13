#include <stdio.h>
#include <signal.h>
#include "Signal.h"
/*
1. Only signals of the type currently being processed by the handler are blocked.
2. As with all signal implementations, signals are not queued.
3. Interrupted system calls are automatically restarted whenever possible.
*/


handler_t *Signal(int signum, handler_t *handler)
{
  struct sigaction action, old_action;

  action.sa_handler = handler;
  sigemptyset(&action.sa_mask); /* block sigs of type being handled */
  action.sa_flags = SA_RESTART; /* Restart syscalls if possible */

  if(sigaction(signum, &action, &old_action) < 0)
    fprintf(stderr,"failed to install signal handler\n");

  return (old_action.sa_handler);
}


