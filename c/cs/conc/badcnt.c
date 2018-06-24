#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>


void *thread(void *vargp);  /* thread routine prototype */

/* global shared variable */
volatile int cnt = 0;

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

/* thread routine */
void *thread(void *vargp)
{
    int i, nIters = *((int *)vargp);

    for (i = 0; i < nIters; i++)
        cnt++;

    return NULL;
}


