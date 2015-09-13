#include<pthread.h>
#include<stdio.h>
#define NUM_THREADS 5

void* runner(void*);

int main (int argc, char *argv[])
{
  int i, policy;

  pthread_t tid[NUM_THREADS]; /* the thread identifiers */
  pthread_attr_t attr; /* set of thread attributes */

  /* get the default attribute */
  pthread_attr_init(&attr);

  /* get the current scheduling policy */
  if(pthread_attr_getschedpolicy(&attr,&policy) != 0)
    fprintf(stderr, "Unable to get policy.\n");
  else{
    printf("Scheduling policy is ...");
    if(policy == SCHED_OTHER)
      printf("SCHED_OTHER\n");
    else if (policy == SCHED_RR)
      printf("SCHED_RR\n");
    else if (policy == SCHED_FIFO)
      printf("SCHED_FIFO\n");
    else
      fprintf(stderr,"Unknown scheduling policy.\n");
  }

  /* set the scheduling policy - FIFO, RR, or OTHER */
  if(pthread_attr_setschedpolicy(&attr,SCHED_FIFO) != 0)
    fprintf(stderr,"Unable to set policy.\n");

  /* get the current scheduling policy */
  if(pthread_attr_getschedpolicy(&attr,&policy) != 0)
    fprintf(stderr, "Unable to get policy.\n");
  else{
    printf("Scheduling policy is now ...");
    if(policy == SCHED_OTHER)
      printf("SCHED_OTHER\n");
    else if (policy == SCHED_RR)
      printf("SCHED_RR\n");
    else if (policy == SCHED_FIFO)
      printf("SCHED_FIFO\n");
    else
      fprintf(stderr,"Unknown scheduling policy.\n");
  }


  /* create the threads */
  for (i = 0; i < NUM_THREADS; i++)
    pthread_create(&tid[i], &attr, runner, NULL);

  /* now join on each thread */
  for (i = 0; i < NUM_THREADS; i++)
    pthread_join(tid[i], NULL);

  return 0;
}

/* The thread will begin control in this function */
void *runner(void *param)
{

  printf("Some thread is now running\n");
  pthread_exit(0);
}
