#include <stdio.h>
#include <semaphore.h>
#include <pthread.h>

#include "rio.h"
#include "echo_cnt.h"

#define MAXLINE 8192



static int byte_cnt;    /* byte counter */
static sem_t mutex;     /* and the mutex that protects it */


static void P(sem_t *s) { sem_wait(s); }
static void V(sem_t *s) { sem_post(s); }

static void init_echo_cnt()
{
    sem_init(&mutex, 0, 1);
    byte_cnt = 0;
}


void echo_cnt(int connfd)
{

    int n;
    char buf[MAXLINE];
    rio_t rio;
    static pthread_once_t once = PTHREAD_ONCE_INIT;

    pthread_once(&once,init_echo_cnt);
    rio_readinitb(&rio,connfd);

    while ((n = rio_readlineb(&rio, buf, MAXLINE)) != 0) {
        P(&mutex);
        byte_cnt += n;
        printf("thread %d received %d (%d total) bytes on fd %d\n",
                (int) pthread_self(), n, byte_cnt, connfd);
        V(&mutex);
        rio_writen(connfd, buf, n);
    }
}


