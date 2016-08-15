#include <sys/types.h>
#include <sys/msg.h>
#include "tlpi_hdr.h"

int
main(int argc, char *argv[])
{
  struct msqid_ds ds;
  int msqid;

  if (argc != 3 || strcmp(argv[1], "--help") == 0)
    usageErr("%s msqid max-bytes\n", argv[0]);
  
  /* Retrieve copy of associated data structure from kernel */

  msqid = getInt(argv[1], 0, "msqid");
  if (msgctl(msqid, IPC_STAT, &ds) == -1)
    errExit("msgctl");

  ds.msg_qbytes = getInt(argv[2], 0, "max-bytes");
  
  /* Update associated data structure in kernel */

  if (msgctl(msqid, IPC_SET, &ds) == -1)
    errExit("msgctl");

  exit(EXIT_SUCCESS);
}
