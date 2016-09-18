/* Using sem_getvalue to retrieve the value of a POSIX semaphore */
/* link with -pthread */

#include <semaphore.h>
#include "tlpi_hdr.h"

int
main(int argc, char *argv[])
{
  int value;
  sem_t *sem;

  if (argc != 2)
    usageErr("%s sem-name\n", argv[0]);

  sem = sem_open(argv[1], 0);
  if (sem == SEM_FAILED)
    errExit("sem_open");

  if (sem_getvalue(sem, &value) == -1)
    errExit("sem_getvalue");

  printf("%d\n", value);

  exit(EXIT_SUCCESS);
}
