#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include "hacking.h"

#define PORT 7890 // The port users will be connecting to


int main(void) {
  int sockfd, new_sockfd;   // Listen on sock_fd, new connection on new_fd
  struct sockaddr_in host_addr, client_addr;  // My address information
  socklen_t sin_size;
  int recv_length=1, yes=1;
  char buffer[1024];
  
  if ((sockfd = socket(PF_INET, SOCK_STREAM, 0)) == -1)
    fatal("in socket");

  // SO_REUSEADDR options allows binding to socket even if it appears to be in use
  // we are passing data to function via a pointer to data and its size
  if (setsockopt(sockfd, SOL_SOCKET, SO_REUSEADDR, &yes, sizeof(int)) == -1)
    fatal("setting socket option SO_REUSEADDR");

  host_addr.sin_family = AF_INET;         // Host byte order
  host_addr.sin_port = htons(PORT);       // Short, network byte order
  host_addr.sin_addr.s_addr = 0;          // Automatically fill with my IP.
  memset(&(host_addr.sin_zero), '\0', 8); // Zero the rest of the struct.

  if (bind(sockfd, (struct sockaddr *)&host_addr, sizeof(struct sockaddr)) == -1)
    fatal("binding to socket");

  if (listen(sockfd, 5) == -1)    // 5 is maximum size of backlog queue
    fatal("listening on socket");

  while(1) {  // Accept loop.
    sin_size = sizeof(struct sockaddr_in);
    new_sockfd = accept(sockfd, (struct sockaddr *)&client_addr, &sin_size);
    if(new_sockfd == -1)
      fatal("accepting connection");
    printf("server: got connection from %s port %d\n",
      inet_ntoa(client_addr.sin_addr), ntohs(client_addr.sin_port));
    send(new_sockfd, "Hello, world!\n", 14, 0);
    recv_length = recv(new_sockfd, &buffer, 1024, 0);
    while(recv_length > 0) {
      printf("RECV: %d bytes\n", recv_length);
      dump(buffer, recv_length);
      recv_length = recv(new_sockfd, &buffer, 1024, 0);
    }

    close(new_sockfd);
  }
  
  return 0;
}


