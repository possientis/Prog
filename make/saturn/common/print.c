#if HAVE_CONFIG_H
# include <config.h>
#endif

#include "satcommon.h"

#include <stdio.h>
#include <stdlib.h>

#if HAVE_PTHREAD_H
# include <pthread.h>
#endif



static void * print_it(void * data)
{
  printf("Hello from %s!\n", (const char*) data);
  return 0;
}

int print_routine(const char * name)
{
#if ASYNC_EXEC
  printf("pthread version is running\n");
  pthread_t tid;
  pthread_create(&tid, 0, print_it, (void*)name);
  pthread_join(tid, 0);
#else
  printf("single thread version is running\n");
  print_it(name);
#endif
  return 0;
}

