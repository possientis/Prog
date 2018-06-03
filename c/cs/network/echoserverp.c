#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <signal.h>
#include <arpa/inet.h>
#include <sys/wait.h>

#include "connect.h"
#include "rio.h"

#define MAXLINE 8192


void echo(int connfd);

void sigchld_handler(int sig)
{
    while (waitpid(-1, 0, WNOHANG) > 0)
        ;
    return;
}

int main(int argc, char **argv)
{
    int listenfd, connfd, port;
    socklen_t clientlen = sizeof(struct sockaddr_in);
    struct sockaddr_in clientaddr;

    if (argc != 2) {
        fprintf(stderr, "usage: %s <port>\n", argv[0]);
        exit(0);
    }

    port = atoi(argv[1]);

    if (signal(SIGCHLD, sigchld_handler) == SIG_ERR) {
        fprintf(stderr, "Unable to set up signal handler for SIGCHLD\n");
        exit(1);
    }

    if ((listenfd = open_listenfd(port)) == -1) {
        fprintf(stderr, "Unable to set up listening socket on port %d\n", port);
        exit(1);
    }

    while (1) {
        connfd = accept(listenfd, (SA *) &clientaddr, &clientlen);
        if (fork() == 0) {  /* child */
            close(listenfd);    /* child closes listening socket */
            echo(connfd);       /* child services client */
            close(connfd);      /* child closes connection with client */
            exit(0);            /* child exits */
        }
        close(connfd);          /* parent closes connection socket (imporant !) */
    }

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
