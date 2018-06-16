#include <stdio.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <pthread.h>

#include "rio.h"
#include "connect.h"

#define MAXLINE 8192

void *thread(void *vargp);
void echo(int connfd);


int main(int argc, char **argv)
{

    int listenfd, *connfdp, port;
    socklen_t clientlen = sizeof(struct sockaddr_in);
    struct sockaddr_in clientaddr;
    pthread_t tid;

    if (argc != 2) {
        fprintf(stderr, "usage: %s <port>\n", argv[0]);
        exit(0);
    }

    port = atoi(argv[1]);

    if ((listenfd = open_listenfd(port)) < 0) {
        fprintf(stderr, "unabled to open listening socket on port %d\n", port);
        exit(1);
    }

    while (1) {
        if ((connfdp = malloc(sizeof(int))) == NULL) {
            fprintf(stderr, "out of memory error\n");
            exit(1);
        }
        *connfdp = accept(listenfd, (SA *) &clientaddr, &clientlen);
        pthread_create(&tid, NULL, thread, connfdp);
    }
}

void *thread(void *vargp)
{
    int connfd = *((int *)vargp);
    /* resources automatically freed when terminating, 
     * main thread does not need to reap thread explicitly
     */
    pthread_detach(pthread_self()); 
    free(vargp);
    echo(connfd);
    close(connfd);
    return NULL;
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
