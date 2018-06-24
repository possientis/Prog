#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <semaphore.h>


void *thread(void *vargp);  /* thread routine prototype */

/* global shared variable */
volatile int cnt = 0;

sem_t mutex;    /* semaphore that protects counter */


int main(int argc, char **argv)
{
    int nIters;
    pthread_t tid1, tid2;

    /* check input arguments */
    if (argc != 2) {
        printf("usage: %s <number of iterations>\n", argv[0]);
        exit(0);
    }

    nIters = atoi(argv[1]);

    sem_init(&mutex, 0, 1); /* initializing mutex */

    /* create threads and wait for them to finish */
    pthread_create(&tid1, NULL, thread, &nIters);
    pthread_create(&tid2, NULL, thread, &nIters);
    pthread_join(tid1, NULL);
    pthread_join(tid2, NULL);

    /* check result */
    if (cnt != (2 * nIters))
        printf("BOOM! cnt = %d\n", cnt);
    else
        printf("OK cnt = %d\n", cnt);

    exit(0);
}

void P(sem_t *s) { sem_wait(s); }
void V(sem_t *s) { sem_post(s); }

/* thread routine */
void *thread(void *vargp)
{
    int i, nIters = *((int *)vargp);

    for (i = 0; i < nIters; i++) {
        P(&mutex);
        cnt++;
        V(&mutex);
    }

    return NULL;
}


