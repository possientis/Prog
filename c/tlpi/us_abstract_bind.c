#include <sys/socket.h>
#include <sys/un.h>

int main(){

  struct sockaddr_un addr;
  int sockfd;

  memset(&addr, 0, sizeof(struct sockaddr_un));  /* Clear address structure */
  addr.sun_family = AF_UNIX;  /* UNIX domain address */

  /* addr.sun_path[0] has already been set to 0 by memset() */

  strncpy(&addr.sun_path[1], "xyz", sizeof(addr.sun_path) - 2);
              /* Abstract name is "xyz" followed by null bytes */

  sockfd = socket(AF_UNIX, SOCK_STREAM, 0);
  if (sockfd == -1)
    errExit("socket");

  if (bind(sockfd, (struct sockaddr *) &addr,
        sizeof(struct sockaddr_un)) == -1)
    errExit("bind");
}
