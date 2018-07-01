#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

#define N 10

void *thread(void* vargp);

int main()
{
    pthread_t tid[N];
    int i;

    /* passing unprotected shared address &i */
    i= 0;
    while (i < N) {
        printf("main thread creating thread %d\n", i);
        pthread_create(&tid[i], NULL, thread, &i);
        i += 1;
    }

    for (i = 0; i < N; i++)
        pthread_join(tid[i],NULL);

    exit(0);
}

void *thread(void *vargp)
{
    int myid = *((int *)vargp);
    printf("Hello from thread %d\n", myid);
    return NULL;
}
