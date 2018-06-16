#include <stdio.h>
#include <pthread.h>

#define N 2

void *thread(void *vargp);

const char **ptr; /* global variable */

int main()
{
    int i;
    pthread_t tid;

    const char *msgs[N] = { 
        "Hello from foo", 
        "Hello from bar"
    };       


    ptr = msgs;
    for (i = 0; i < N; i++)
        pthread_create(&tid, NULL, thread, (void *) (long) i);
        
    pthread_exit(NULL);

}


void *thread(void *vargp)
{
    int myid = (int) (long) vargp;
    static int cnt = 0;

    printf("[%d]: %s (cnt=%d)\n", myid, ptr[myid], ++cnt);

    return NULL;
}

