#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>

#include "hacking.h"
#include "hacking-network.h"


int main(int argc, char *argv[]) {

  int sockfd;
  struct hostent *host_info;
  struct sockaddr_in target_addr;
  unsigned char buffer[4096];

  if(argc < 2) {
    printf("Usage: %s <hostname>\n", argv[0]);
    exit(1);
  }


