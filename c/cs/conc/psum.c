#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#define MAXTHREADS 32

void *sum(void *vargp);

/* global shared variables */
long psum[MAXTHREADS];  /* partial sum computed by each thread */
long nelems_per_thread; /* number of elements summed by each thread */

int main(int argc, char **argv)
{
    long i, nelems, log_nelems, nthreads, result = 0;
    pthread_t tid[MAXTHREADS];
    int myid[MAXTHREADS];

    /* get input arguments */
    if (argc != 3) {
        printf("Usage: %s <nthreads> <log_nelems>\n", argv[0]);
        exit(0);
    }

    nthreads = atoi(argv[1]);

    if (nthreads <= 0) {
        fprintf(stderr, "<nthreads> should be at least 1\n");
        exit(1);
    }

    if (nthreads > MAXTHREADS) {
        fprintf(stderr, "<nthreads> cannot exceed %d\n", MAXTHREADS);
        exit(1);
    }

    log_nelems = atoi(argv[2]);
    nelems = (1L << log_nelems);
    nelems_per_thread = nelems / nthreads;

    /* create peer threads and wait for them to finish */
    for (i = 0; i < nthreads; i++) {
        myid[i] = i;
        pthread_create(&tid[i], NULL, sum, &myid[i]);
    }

    for (i = 0; i < nthreads; i++)
        pthread_join(tid[i], NULL);

    /* add up the partial sums computed by each thread */
    for (i = 0; i < nthreads; i++)
        result += psum[i];

    /* check final answer */
    if (result != (nelems*(nelems - 1))/2)
        printf("Error: result = %ld\n", result);
    else
        printf("Correct: result = %ld\n", result);

    exit(0);
}


void *sum(void *vargp)
{
    int myid = *((int *)vargp);     /* extract the thread id */
    long start = myid * nelems_per_thread;
    long end = start + nelems_per_thread;
    long i, sum= 0;

    for (i = start; i < end; i++)
        sum += i;

    psum[myid] = sum;

    return NULL;
}
