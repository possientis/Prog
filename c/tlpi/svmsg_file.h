#include <sys/types.h>
#include <sys/msg.h>
#include <sys/stat.h>
#include <stddef.h>
#include <limits.h>
#include <fcntl.h>
#include <signal.h>
#include <sys/wait.h>
#include"tlpi_hdr.h"

#define SERVER_KEY 0x1aaaaaa1 /* Key for server's message queue */

struct requestMsg {           /* Requests (client to server) */
  long mtype;                 /* unused */
  int clientId;               /* ID of client's message queue */
  char pathname[PATH_MAX];    /* file to be returned */
}; 

/* REQ_MSG_SIZE computes size of 'mtext' part of 'requestMsg' structure.
 * We use offsetof() to handle the possibility that there are padding
 * bytes between the 'clientId' and 'pathname' fields. */









