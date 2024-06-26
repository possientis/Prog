/* Using mq_unlink() to unlink a POSIX message queue */
/* need to link aginst realtime library librt to use POSIX IPC */

/* gcc filename error_functions.c -lrt */

#include <mqueue.h>
#include "tlpi_hdr.h"

int
main(int argc, char *argv[])
{
  if (argc != 2 || strcmp(argv[1], "--help") == 0)
    usageErr("%s mq-name\n", argv[0]);

  if (mq_unlink(argv[1]) == -1)
    errExit("mq_unlink");

  exit(EXIT_SUCCESS);
}
