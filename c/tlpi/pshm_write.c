/* Copying data into a POSIX shared memory object */
/* link with -lrt */
#include <fcntl.h>
#include <sys/mman.h>
#include "tlpi_hdr.h"

int
main(int argc, char *argv[])
{
  int fd;
  size_t len;  /* Size of shared memory object */
  char *addr;

  if (argc != 3 || strcmp(argv[1], "--help") == 0)
    usageErr("%s shm-name string\n", argv[0]);

  fd = shm_open(argv[1], O_RDWR, 0);  /* Open existing object */
  if (fd == -1)
    errExit("shm_open");

  len = strlen(argv[2]);
  if (ftruncate(fd, len) == -1)      /* Resize object to hold string */
    errExit("ftruncate");

  printf("Resized to %ld bytes\n", (long) len);

  addr = mmap(NULL, len, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
  if (addr == MAP_FAILED)
    errExit("mmap");

  if (close(fd) == -1)
    errExit("close");  /* 'fd' is no longer needed */

  printf("copying %ld bytes\n", (long) len);
  memcpy(addr, argv[2], len);  /* Copy string to shared memory */

  exit(EXIT_SUCCESS);
}
