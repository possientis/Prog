// sh -c "ls -l | wc"....
// sh -c "mycommand"

// this simple implementation of system does not provide
// a correct treatment of signals.
#include <unistd.h>
#include <sys/wait.h>
#include <sys/types.h>

int
system(char *command)
{
  int status;
  pid_t childPid;

  switch (childPid = fork()) {
    case -1: /* Error */
      return -1;

    case 0: /* Child */
      execl("/bin/sh", "sh", "-c", command, (char *) NULL);
      _exit(127);      /* Failed exec */

    default: /* Parent */
      if (waitpid(childPid, &status, 0) == -1)
        return -1;
      else
        return status;
  }
}
