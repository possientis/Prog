#include <pthread.h>
#include<semaphore.h>
#include <stdio.h>

void* sellTickets(void*);
static const int NUM_THREADS = 5;
static sem_t startSale;
static sem_t saleLock;


struct Data {

  int agentID;
  int* pNumTicketsLeft;
  int counter;

};


int main (int argc, char* argv[])
{

  int NumTicketsLeft = 150;
  Data arg[NUM_THREADS];

  /* initializing the semaphore */
  sem_init(&startSale,0,0); // initial value 0
  sem_init(&saleLock,0,1);  // initial value 1

  /* the thread identifiers */
  pthread_t tid[NUM_THREADS];

  /* the set of thread attributes */
  pthread_attr_t attr;

  /* get the default attribute */
  pthread_attr_init(&attr);


  /* create the threads */
  for (int i = 0; i < NUM_THREADS; i++){

    // setting up argument for thread
    arg[i].agentID = i;
    arg[i].pNumTicketsLeft = &NumTicketsLeft;
    arg[i].counter = 0;

    printf("Creating thread n.%d\n",i);
    pthread_create(&tid[i], &attr, sellTickets, &arg[i]);

//  for(int j = 0 ; j < 100000; j++);

  }

  // allowing threads to run
  for(int i = 0; i < NUM_THREADS; i++)
    sem_post(&startSale);

  /* waiting for all threads to terminate */
  for (int i =  0; i < NUM_THREADS; i++)
    pthread_join(tid[i], NULL);


  int sum = 0;
  for (int i = 0; i < NUM_THREADS; i++)
  {
    printf("Agent n.%d has sold %d tickets\n",i,arg[i].counter);
    sum += arg[i].counter;
  }

  printf("Total number of tickets sold is %d\n",sum);

  printf("The main thread is exiting now\n");

  return 0;

}

/* the threads will begin control in this function */
void* sellTickets(void* arg)
{

  sem_wait(&startSale);

  Data *ptemp = (Data*) arg;
  int agentID = ptemp->agentID;
  int *pNumTicketsLeft = ptemp->pNumTicketsLeft;
  int *pCounter = &ptemp->counter;
  int ticket;

  printf("Agent n.%d is running\n",agentID);

  while(true)
  {
    sem_wait(&saleLock);
    if(*pNumTicketsLeft == 0) break;
    ticket = *pNumTicketsLeft;
    (*pNumTicketsLeft)--;
    sem_post(&saleLock);
    printf("Agent n.%d selling ticket n. %d\n",agentID, ticket);
    (*pCounter)++;
    for(int j = 0; j < 100000; j++);
  }

  sem_post(&saleLock);

  printf("Agent n.%d is exiting\n",agentID);

  pthread_exit(0);

}
