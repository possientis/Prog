#include <stdio.h>
#include <stdlib.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <unistd.h>

#include "rio.h"
#include "connect.h"

#define MAXLINE 8192

void echo(int connfd);

int main(int argc, char **argv)
{
    int listenfd, connfd, port, clientlen;
    struct sockaddr_in clientaddr;
    struct hostent *hp;
    char *haddrp;

    if (argc != 2) {
        fprintf(stderr, "usage: %s <port>\n", argv[0]);
        exit(0);
    }

    port = atoi(argv[1]);

    if ((listenfd = open_listenfd(port)) < 0) {
        fprintf(stderr, "Unable to open listening socket on port %d\n", port);
        exit(127);
    }

    printf("Established listening socket on port %d\n", port);

    while (1) {
        clientlen = sizeof(clientaddr);
        if ((connfd = accept(listenfd, (SA *)&clientaddr, &clientlen)) < 0) {
            fprintf(stderr, "Accept error, exiting.\n");
            exit(127);
        }
        /* determine domain name and IP address of client */
        hp = gethostbyaddr((const char *)&clientaddr.sin_addr.s_addr,
                           sizeof(clientaddr.sin_addr.s_addr), AF_INET);
        haddrp = inet_ntoa(clientaddr.sin_addr);

        printf("server connected to %s (%s)\n", hp->h_name, haddrp);

        echo(connfd);

        printf("server closing connection\n");

        close(connfd);
    }

    exit(0);
}



void echo(int connfd)
{
    size_t n;
    char buf[MAXLINE];
    rio_t rio;

    rio_readinitb(&rio, connfd);

    while((n = rio_readlineb(&rio, buf, MAXLINE)) != 0) {
        printf("server received %d bytes\n", n);
        rio_writen(connfd, buf, n);
    }
}
