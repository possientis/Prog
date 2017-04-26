#include <pthread.h>
extern int a, c;
extern volatile int b;

void *thread1(void* data){

  a = 1;
  b = 1;

  pthread_exit(0);
}
