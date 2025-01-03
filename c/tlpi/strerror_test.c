/* Calling strerror() from two different threads */

#include <stdio.h>
#include <string.h>/* Get declaration of strerror() */
#include <pthread.h>
#include "tlpi_hdr.h"

static void *
threadFunc(void *arg)
{
  char *str;

  printf("Other thread about to call strerror()\n");
  str = strerror(EPERM);
  printf("Other thread: str (%p) = %s\n", str, str);

  return NULL;
}


int
main(int argc, char *argv[])
{
  pthread_t t;
  int s;
  char *str;

  str = strerror(EINVAL);
  printf("Main thread has called strerror()\n");

  s = pthread_create(&t, NULL, threadFunc, NULL);
  if (s != 0)
    errExitEN(s, "pthread_create");

  s = pthread_join(t, NULL);
  if (s != 0)
    errExitEN(s, "pthread_join");
  
  printf("Main thread: str (%p) = %s\n", str, str);

  exit(EXIT_SUCCESS);
}
