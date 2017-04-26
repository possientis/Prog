#include <pthread.h>
extern int a,c;
extern volatile int b;

void *thread2(void* data){

  while(b == 0);

  c = a;

  pthread_exit(0);
}
