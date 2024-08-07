#if HAVE_CONFIG_H
# include <config.h>
#endif

#if HAVE_STDINT_H
# include <stdint.h>
#elif HAVE_INTTYPES_H
# include <inttypes.h>
#endif

#include <stdio.h>
#include <stdlib.h>

#if HAVE_PTHREAD_H
# include <pthread.h>
#endif


static void * print_it(void * data)
{
  uint16_t x = 23;
  uint64_t y = 345;

  printf("Hello from %s!\n", (const char*) data);
  return 0;
}

int main(int argc, char * argv[])
{
#if ASYNC_EXEC
  printf("pthread version is running\n");
  pthread_t tid;
  pthread_create(&tid, 0, print_it, argv[0]);
  pthread_join(tid, 0);
#else
  printf("single thread version is running\n");
  print_it(argv[0]);
#endif
  return 0;
}
