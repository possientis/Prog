// Usually the parent is scheduled before the child. 
// However, do not rely on this behaviour for correctness

#include <sys/wait.h>
#include "tlpi_hdr.h"

int
main(int argc, char *argv[])
{
  int numChildren, j;
  pid_t childPid;

  if (argc > 1 && strcmp(argv[1], "--help") == 0)
    usageErr("%s [num-children]\n", argv[0]);

  numChildren = (argc > 1) ? getInt(argv[1], GN_GT_0, "num-children") : 1;

  setbuf(stdout, NULL);  /* Make stdout unbuffered */

  for (j = 0; j < numChildren; j++) {
    switch (childPid = fork()) {
      case -1:
        errExit("fork");

      case 0:
        printf("%d child\n", j);
        _exit(EXIT_SUCCESS);

      default:
        printf("%d parent\n", j);
        wait(NULL);    /* Wait for child to terminate */
        break;
    }
  }

  exit(EXIT_SUCCESS);
}
