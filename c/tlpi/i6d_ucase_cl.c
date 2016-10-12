/* IPv6 case-conversion client using datagram sockets */

#include "i6d_ucase.h"

int
main(int argc, char *argv[])
{
  struct sockaddr_in6 svaddr;
  int sfd, j;
  size_t msgLen;
  ssize_t numBytes;
  char resp[BUF_SIZE];

  if (argc < 3 || strcmp(argv[1], "--help") == 0)
    usageErr("%s host-address msg...\n", argv[0]);

  sfd = socket(AF_INET6, SOCK_DGRAM, 0);  /* Create client socket */
  if (sfd == -1)
    errExit("socket");

  memset(&svaddr, 0, sizeof(struct sockaddr_in6));
  svaddr.sin6_family = AF_INET6;
  svaddr.sin6_port = htons(PORT_NUM); /* host to network endianness */
  /* converts string representation of IPv6 address to actual address */
  if (inet_pton(AF_INET6, argv[1], &svaddr.sin6_addr) <= 0)
    fatal("inet_pton failed for address '%s'", argv[1]);

  /* Send messages to server; echo responses on stdout */

  for (j = 2; j < argc; j++) {
    msgLen = strlen(argv[j]);
    if (sendto(sfd, argv[j], msgLen, 0, (struct sockaddr *) &svaddr,
          sizeof(struct sockaddr_in6)) != msgLen)
      fatal("sendto");

    /* should block */
    numBytes = recvfrom(sfd, resp, BUF_SIZE, 0, NULL, NULL);
    if (numBytes == -1)
      errExit("recvfrom");

    printf("Response %d: %.*s\n", j - 1, (int) numBytes, resp);
  }

  exit(EXIT_SUCCESS);
}
