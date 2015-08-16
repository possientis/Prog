#include <pthread.h>
#include <semaphore.h>
#include <stdio.h>

#define BUFFER_SIZE 8

void* consumerThread(void*);
void* producerThread(void*);

static char buffer[BUFFER_SIZE];
static sem_t emptySlots;
static sem_t fullSlots;

int main (int argc, char* argv[])
{

  printf("Consumer producer simulation running...\n");

  sem_init(&emptySlots,0,BUFFER_SIZE);  // all buffer slots are empty

  sem_init(&fullSlots,0,0);             // none of the buffer slots are full

  pthread_t tid[2];     // one consumer (reader) and one producer (writer) thread

  pthread_attr_t attr;  // set of thread attributes

  pthread_attr_init(&attr); // get default attributes

  printf("Creating consumer thread...\n");

  pthread_create(&tid[0],&attr,consumerThread,nullptr);

  printf("Creating producer thread...\n");

  pthread_create(&tid[1],&attr,producerThread, nullptr);

  pthread_join(tid[0],nullptr); // waiting for consumer thread to terminate

  pthread_join(tid[1],nullptr); // waiting for producer thread to terminate

  printf("Comsumer producer simulation exiting...\n");

return 0;
}

void* consumerThread(void*)
{
  printf("Consumer thread starting ...\n");

  int index = 0;
  char c;

  while(true)
  {
    sem_wait(&fullSlots);
    c = buffer[index % BUFFER_SIZE];
    printf("consumer receiving character %c\n",c);
    sem_post(&emptySlots);
    index++;
    if(c == 0) break;
  //  printf("%c",c);
  }

//  printf("\n");

  printf("Consumer thread exiting...\n");

}

void* producerThread(void*)
{

  printf("Producer thread starting...\n");

  const char *message = "The following message contains very little worthy information and may be ignored by its recipient without long term implications";

  int index = 0;

  for(const char* ptr = message; *ptr != 0; ptr++)
  {
    sem_wait(&emptySlots);  // waiting for some slots to be empty
    printf("producer sending character %c\n",*ptr);
    buffer[index % BUFFER_SIZE] = *ptr;
    sem_post(&fullSlots);
    index++;
  }

  sem_wait(&emptySlots);
  printf("producer marking end of message\n");
  buffer[index % BUFFER_SIZE] = 0;  // sending end of message notification
  sem_post(&fullSlots);

 printf("Producer thread exiting...\n");

}
