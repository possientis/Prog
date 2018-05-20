#include <stdio.h>
#include <string.h>
#include <unistd.h>

#include "rio.h"
#include "connect.h"

#define MAXLINE 8192

int main(int argc, char **argv)
{
    int clientfd, port;
    char *host, buf[MAXLINE];
    rio_t rio;

    if (argc != 3) {
        fprintf(stderr, "usage: %s <host> <port>\n", argv[0]);
        exit(0);
    }

    host = argv[1];
    port = atoi(argv[2]);

    if ((clientfd = open_clientfd(host, port)) < 0) {
        fprintf(stderr, "failed to connect to host %s on port %d\n", host, port);
        exit(127);
    }

    rio_readinitb(&rio, clientfd);

    /* should add error handling to fgets and other functions here */
    while (fgets(buf, MAXLINE, stdin) != NULL) {
        rio_writen(clientfd, buf, strlen(buf));
        rio_readlineb(&rio, buf, MAXLINE);
        fputs(buf, stdout);
    }

    close(clientfd);
    exit(0);

}
