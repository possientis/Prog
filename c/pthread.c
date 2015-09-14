#include<pthread.h>
#include<unistd.h>  // getpid
#include<stdio.h>
#define NUM_THREADS 5

void* runner(void*);

int main (int argc, char *argv[])
{
  int i, scope;

  pthread_t tid[NUM_THREADS]; /* the thread identifiers */
  pthread_attr_t attr; /* set of thread attributes */

  /* get the default attribute */
  pthread_attr_init(&attr);


  /* first inquire on the current scope */
  if(pthread_attr_getscope(&attr, &scope) != 0)
    fprintf(stderr, "Unable to get scheduling scope\n");
  else {
    if (scope == PTHREAD_SCOPE_PROCESS)
      printf("PTHREAD_SCOPE_PROCESS\n");
    else if (scope == PTHREAD_SCOPE_SYSTEM)
      printf("PTHREAD_SCOPE_SYSTEM\n");
    else
      fprintf(stderr, "Illegal scope value.\n");
  }
  /* set the scheduling algorithm to SCS */
  pthread_attr_setscope(&attr, PTHREAD_SCOPE_SYSTEM);

  /* create the threads */
  for (i = 0; i < NUM_THREADS; i++)
    pthread_create(&tid[i], &attr, runner, NULL);

  /* now join on each thread */
  for (i = 0; i < NUM_THREADS; i++)
    pthread_join(tid[i], NULL);

  return 0;
}

/* The thread will begin control in this function */
void* runner(void *param)
{

  printf("Some thread is now running with pid %d\n",getpid());
  pthread_exit(0);
}
