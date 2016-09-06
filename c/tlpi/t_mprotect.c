#define _BSD_SOURCE  /* Get MAP_ANONYMOUS definition from <sys/mman.h> */
#include <sys/mman.h>
#include "tlpi_hdr.h"

#define LEN (1024 * 1024)

#define SHELL_FMT "cat /proc/%ld/maps | grep zero"
#define CMD_SIZE (sizeof(SHELL_FMT) + 20)
                            /* Allow extra space for integer string */
int
main(int argc, char *argv[])
{
  char cmd[CMD_SIZE];
  char *addr;

  /* Create an anonymous mapping with all access denied */

  addr = mmap(NULL, LEN, PROT_NONE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  if (addr == MAP_FAILED)
    errExit("mmap");

  /* Display line from /proc/self/maps corresponding to mapping */

  printf("Before mprotect()\n");
  snprintf(cmd, CMD_SIZE, SHELL_FMT, (long) getpid());
  system(cmd);

  /* Change protection on memory to allow read and write access */

  if (mprotect(addr, LEN, PROT_READ | PROT_WRITE) == -1)
    errExit("mprotect");

  printf("After mprotect()\n");
  system(cmd);  /* Review protection via /proc/self/maps */

  exit(EXIT_SUCCESS);
}
