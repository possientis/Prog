// do not use vfork, use fork: slightly less efficient but better semantics
// Nowadays, fork is implemented with 'copy-on-write' and is pretty efficient
// vfork allows child and parent to share memory, which may create chaos
// vfork should be followed (for the child) by a call to exec
// and if this calls fails by _exit. Do not use exit (as this would cause
// the stdio buffers of the parent to be flushed and closed.
// And if you do use vfork, likelihood is prograom is not portable.
// parent execution is suspended after vfork until child exec or _exit
#include "tlpi_hdr.h"

int
main(int argc, char *argv[])
{
  int istack = 222;

  switch (vfork()) {
    case -1:
      errExit("vfork");
    case 0:      /* Child executes first, in parent's memory space */
      sleep(3);      /* Even if we sleep for a while,
                      * parent still is not scheduled */
      write(STDOUT_FILENO, "Child executing\n", 16);
      istack *= 3;      /* This change will be seen by parent */
      _exit(EXIT_SUCCESS);

    default:      /* Parent is blocked until child exits */
      write(STDOUT_FILENO, "Parent executing\n", 17);
      printf("istack=%d\n", istack);
      exit(EXIT_SUCCESS);
  }
}
