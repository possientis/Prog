#include <stdio.h>
#include <sys/shm.h>
#include <sys/stat.h>

int main()
{
  /* the identifier for the shared memory segment */
  int segment_id;
  /* a pointer to the shared memory segment */
  char *shared_memory;
  /* the size (in bytes) of the shared memory segment */
  const int size =4096;

  /* allocate the shared memory segment */
  segment_id = shmget(IPC_PRIVATE, size, S_IRUSR | S_IWUSR);

  /* attach the shared memory segment */
  shared_memory = (char *) shmat(segment_id,NULL, 0);

  /* write a message to the shared memory segment */
  sprintf(shared_memory, "Hi there!");

  /* now print out the string from shared memory */
  printf("*%s\n", shared_memory);

  /* now detach the shared memory segment */
  shmdt(shared_memory);

  /* now remover the shared memory segment */
  shmctl(segment_id, IPC_RMID, NULL);

  return 0;

}

