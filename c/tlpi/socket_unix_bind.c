/* Binding a UNIX domain socket */
#include <sys/un.h>
#include <sys/socket.h>
#include "tlpi_hdr.h"

main(){

  const char *SOCKNAME = "/tmp/mysock";
  int sfd;
  struct sockaddr_un addr;

  sfd = socket(AF_UNIX, SOCK_STREAM, 0);  /* create socket */
  if (sfd == -1)
    errExit("socket");

  // implementation may have non standard fields which we initialize to 0
  memset(&addr, 0, sizeof(struct sockaddr_un)); /* Clear structure */
  addr.sun_family = AF_UNIX;                    /* UNIX domain address */
  strncpy(addr.sun_path, SOCKNAME, sizeof(addr.sun_path) - 1);

  if (bind(sfd, (struct sockaddr *) &addr, sizeof(struct sockaddr_un)) == -1)
    errExit("bind");

}
