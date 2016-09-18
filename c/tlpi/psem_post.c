/* Using sem_post to increment a POSIX semaphore */
/* link with -pthread */

#include <semaphore.h>
#include "tlpi_hdr.h"

int
main(int argc, char *argv[])
{
  sem_t *sem;

  if (argc != 2)
    usageErr("%s sem-name\n", argv[0]);

  sem = sem_open(argv[1], 0);
  if (sem == SEM_FAILED)
    errExit("sem_open");

  if (sem_post(sem) == -1)
    errExit("sem_post");
  exit(EXIT_SUCCESS);
}


