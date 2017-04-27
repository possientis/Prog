#include <pthread.h>
#include <stdio.h>
#include <assert.h>

// semantics of 'volatile' (culler: page 274): prevents the variable from being
// register allocated, or any memory operation on the variable from being 
// reordered with respect to operations before and after it.
// semantics in C, C++, java, ...  may be slightly different for each case.

volatile int b;  // initialized to 0
int a, c;

extern void *thread1(void*);
extern void *thread2(void*);
void do_experiment();


int main()
{
  printf("(a,b) = (%d,%d)\n", a, b);

  int i;
  for(i = 0; i < 20000; ++i){
    do_experiment();
    assert(c == 1);
  }

  return 0;
}

void do_experiment()
{
  a = 0;
  b = 0;

  pthread_t tid1, tid2;
  pthread_attr_t attr;
  pthread_attr_init(&attr);

  if(pthread_create(&tid1, &attr, thread1, NULL) != 0){
    printf("failed to create first thread\n");
  }    

  if(pthread_create(&tid2, &attr, thread2, NULL) != 0){
    printf("failed to create second thread\n");
  }    

  pthread_join(tid1, NULL);
  pthread_join(tid2, NULL);
}






