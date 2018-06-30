#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <netdb.h>
#include <pthread.h>

#include "echo_cnt.h"
#include "connect.h"
#include "sbuf.h"

#define NTHREADS 4
#define SBUFSIZE 16

void echo_cnt(int connfd);
void *thread(void *vargp);

sbuf_t sbuf;    /* shared buffer for connected descriptors */


int main(int argc, char **argv)
{
    int i, listenfd, connfd, port;
    socklen_t clientlen = sizeof(struct sockaddr_in);
    struct sockaddr_in clientaddr;
    pthread_t tid;

    if (argc != 2) {
        fprintf(stderr, "usage: %s <port>\n", argv[0]);
        exit(0);
    }

    port = atoi(argv[1]);
    sbuf_init(&sbuf, SBUFSIZE);

    if ((listenfd = open_listenfd(port)) < 0) {
        fprintf(stderr, "failed to open listening socket on port %d\n", port);
        exit(1);
    }

    for(i = 0; i < NTHREADS; i++) /* create worker threads */
        pthread_create(&tid, NULL, thread, NULL);

    while (1) {
        printf("server awaiting new connection on port %d\n", port);
        connfd = accept(listenfd, (SA *) &clientaddr, &clientlen);
        printf("new client connection established, waiting for slot...\n");
        sbuf_insert(&sbuf, connfd); /* insert connfd in buffer */
        printf("client has been place in a queue\n");
    }
}


void *thread(void *vargp)
{
    pthread_detach(pthread_self());
    while (1) {
        int connfd = sbuf_remove(&sbuf);    /* remove connfd from buffer */
        echo_cnt(connfd);
        close(connfd);
    }
}



