/* Using the SETALL operation to initialize a System V semaphore set */
#include <sys/types.h>
#include <sys/sem.h>
#include "semun.h"  /* Definition of semun union */
#include "tlpi_hdr.h"

int
main(int argc, char *argv[])
{
  struct semid_ds ds;
  union semun arg;  /* Fourth argument for semctl() */
  int j, semid;

  if (argc < 3 || strcmp(argv[1], "--help") == 0)
    usageErr("%s semid val...\n", argv[0]);

  semid = getInt(argv[1], 0, "semid");

  /* Obtain size of semaphore set */

  arg.buf = &ds;
  if (semctl(semid, 0, IPC_STAT, arg) == -1)
    errExit("semctl");

  if (ds.sem_nsems != argc - 2)
    cmdLineErr("Set contains %ld semaphores, but %d values were supplied\n",
        (long) ds.sem_nsems, argc - 2);

  /* Set up array of values; perform semaphore initialization */

  arg.array = calloc(ds.sem_nsems, sizeof(arg.array[0]));
  if (arg.array == NULL)
    errExit("calloc");

  for (j = 2; j < argc; j++)
    arg.array[j - 2] = getInt(argv[j], 0, "val");

  if (semctl(semid, 0, SETALL, arg) == -1)
    errExit("semctl-SETALL");

  printf("Semaphore values changed (PID=%ld)\n", (long) getpid());

  exit(EXIT_SUCCESS);
}
