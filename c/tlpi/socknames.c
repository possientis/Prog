/* Using getsockname() and getpeername() */

#include "inet_sockets.h"         /* Declares our socket functions */
#include "tlpi_hdr.h"

int
main(int argc, char *argv[])
{
  int listenFd, acceptFd, connFd;
  socklen_t len;                  /* Size of socket address buffer */
  void *addr;                     /* Buffer for socket address */
  char addrStr[IS_ADDR_STR_LEN];

  if (argc != 2 || strcmp(argv[1], "--help") == 0)
    usageErr("%s service\n", argv[0]);

  listenFd = inetListen(argv[1], 5, &len);
  if (listenFd == -1)
    errExit("inetListen");

  connFd = inetConnect(NULL, argv[1], SOCK_STREAM);
  if (connFd == -1)
    errExit("inetConnect");

  acceptFd = accept(listenFd, NULL, NULL);
  if (acceptFd == -1)
    errExit("accept");

  addr = malloc(len);
  if (addr == NULL)
    errExit("malloc");

  if (getsockname(connFd, addr, &len) == -1)
    errExit("getsockname");
  printf("getsockname(connFd):   %s\n",
      inetAddressStr(addr, len, addrStr, IS_ADDR_STR_LEN));
  if (getsockname(acceptFd, addr, &len) == -1)
    errExit("getsockname");
  printf("getsockname(acceptFd): %s\n",
      inetAddressStr(addr, len, addrStr, IS_ADDR_STR_LEN));

  if (getpeername(connFd, addr, &len) == -1)
    errExit("getpeername");
  printf("getpeername(connFd):   %s\n",
      inetAddressStr(addr, len, addrStr, IS_ADDR_STR_LEN));
  if (getpeername(acceptFd, addr, &len) == -1)
    errExit("getpeername");
  printf("getpeername(acceptFd): %s\n",
      inetAddressStr(addr, len, addrStr, IS_ADDR_STR_LEN));

  sleep(30);  /* Give us time to run netstat(8) */
  exit(EXIT_SUCCESS);
}
