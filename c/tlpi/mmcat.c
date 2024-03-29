/* using mmap to create a private file mapping */
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include "tlpi_hdr.h"

int
main(int argc, char *argv[])
{
  char *addr;
  int fd;
  struct stat sb;

  if (argc != 2 || strcmp(argv[1], "--help") == 0)
    usageErr("%s file\n", argv[0]);

  fd = open(argv[1], O_RDONLY);
  if (fd == -1)
    errExit("open");

  /* Obtain the size of the file and use it to specify the size of
   * the mapping and the size of the buffer to be written */
  
  if (fstat(fd, &sb) == -1)
    errExit("fstat");

  addr = mmap(NULL, sb.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
  if (addr == MAP_FAILED)
    errExit("mmap");

  if (write(STDOUT_FILENO, addr, sb.st_size) != sb.st_size)
    fatal("partial/failed write");

  /* added later to test munmap */
  if(munmap(addr, sb.st_size) == -1)
    errExit("munmap");

  exit(EXIT_SUCCESS);
}
