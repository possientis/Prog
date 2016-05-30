#include "tlpi_hdr.h"

int
main(int argc, char *argv[])
{
  char *envVec[] = { "GREET=salut", "BYE=adieu", NULL };
  char *filename;

  if (argc != 2 || strcmp(argv[1], "--help") == 0)
    usageErr("%s pathname\n", argv[0]);

  filename = strrchr(argv[1], '/');
  if (filename != NULL)  /* Get basename from argv[1] */
    filename++;
  else
    filename = argv[1];

  execle(argv[1], filename, "hello world", (char *) NULL, envVec);
  errExit("execle");  /* If we get here, something went wrong */
}
