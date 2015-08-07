// g++ synch.c -pthread
#include <pthread.h>
#include<semaphore.h>
#include <stdio.h>

void* runner(void*);


static const int NUM_THREADS = 5;


static  pthread_mutex_t mutex; // mutex
static sem_t sem;               // or semaphore ...

int main (int argc, char* argv[])
{

  int id[NUM_THREADS];
  for (int i = 0; i < NUM_THREADS; i++)
    id[i]=i;


  /* creating the mutex lock */
  pthread_mutex_init(&mutex, NULL);

  /* initializing the semaphore */
  sem_init(&sem, 0, 1); // initial value 1

  /* the thread identifiers */
  pthread_t tid[NUM_THREADS];

  /* the set of thread attributes */
  pthread_attr_t attr;

  /* get the default attribute */
  pthread_attr_init(&attr);

  /* create the threads */
  for (int i = 0; i < NUM_THREADS; i++){

    pthread_create(&tid[i], &attr, runner, &id[i]);
  }

  /* waiting for all threads to terminate */
  for (int i =  0; i < NUM_THREADS; i++)
    pthread_join(tid[i], NULL);


  printf("The main thread is exiting now\n");

  return 0;

}

/* the threads will begin control in this function */
void* runner (void *param)
{

  int index = *((int*) param);


  //pthread_mutex_lock(&mutex);
  sem_wait(&sem);

  /* start of critical section */

  for (int i = 0; i < 5; i++){

    for (int j = 0; j < 100000; j++);  //wait

    printf("T%d_%d\n", index, i);

  }

  /* end of critical section */

  //pthread_mutex_unlock(&mutex);
  sem_post(&sem);

  pthread_exit(0);

}
