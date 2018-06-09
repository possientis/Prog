#include <stdio.h>
#include <arpa/inet.h>
#include <stdlib.h>
#include <unistd.h>

#include "connect.h"
#include "rio.h"

#define MAXLINE 8192

void echo(int connfd);
void command(void);

int main(int argc, char **argv)
{
    int listenfd, connfd, port;

    socklen_t clientlen = sizeof(struct sockaddr_in);
    struct sockaddr_in clientaddr;
    fd_set read_set, ready_set;

    if (argc != 2) {
        fprintf(stderr, "usage: %s <port>\n", argv[0]);
        exit(0);
    }

    port = atoi(argv[1]);
    if ((listenfd = open_listenfd(port)) < 0) {
        fprintf(stderr, "unable to open listening port\n");
        exit(1);
    }
         

    FD_ZERO(&read_set);                 /* clear read set */
    FD_SET(STDIN_FILENO, &read_set);    /* add stdin to read set */ 
    FD_SET(listenfd, &read_set);        /* add listenfd to read set */

    while (1) {
        printf("server waiting for command line or client connection\n");
        ready_set = read_set;
        select(listenfd+1, &ready_set, NULL, NULL, NULL);
        if(FD_ISSET(STDIN_FILENO, &ready_set))
            command();  /* read command line from stdin */
        if(FD_ISSET(listenfd, &ready_set)) {
            connfd = accept(listenfd, (SA *)&clientaddr, &clientlen);
            echo(connfd); /* echo client input until EOF */
            close(connfd);
        }
    }
}

void command() {
    printf("server processing command\n");
    char buf[MAXLINE];
    if(!fgets(buf,MAXLINE,stdin)) {
        printf("server exiting now\n");
        exit(0); /* EOF */
    }

    printf("%s",buf); /* process input command */
}


void echo(int connfd)
{
    size_t n;
    char buf[MAXLINE];
    rio_t rio;

    printf("server processing client request\n");

    rio_readinitb(&rio, connfd);

    while((n = rio_readlineb(&rio, buf, MAXLINE)) != 0) {
        printf("server received %d bytes\n", n);
        rio_writen(connfd, buf, n);
    }
}
