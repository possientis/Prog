// ./a.out
// ./a.out > log; cat log
// very interesting, all to do with stdio buffer in user space


#include "tlpi_hdr.h"

int
main(int argc, char *argv[])
{
  printf("Hello world\n");

  write(STDOUT_FILENO, "Ciao\n", 5);

  if (fork() == -1)
    errExit("fork");

  /* Both child and parent continue execution here */
  exit(EXIT_SUCCESS);
}
