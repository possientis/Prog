#include <stdio.h>
#include <pthread.h>
#include <stdlib.h>

void *thread(void *vargp);



int main()
{
    pthread_t tid;

    if (pthread_create(&tid, NULL, thread, NULL) != 0) {
        fprintf(stderr, "failed to spawn new thread\n");
        exit(1);
    }

    pthread_join(tid, NULL);
    exit(0);

}


void *thread(void *vargp) /* thread routine */
{
    printf("[thread %d]: Hello world!\n", pthread_self());

    return NULL;
}
