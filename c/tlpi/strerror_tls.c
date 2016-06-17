/* a thread-safe implementation of strerror using thread local storage */
#define _GNU_SOURCE /* Get '_sys_nerr' and '_sys_errlist'
                     * declarations from <stdio.h> */
#include <stdio.h>
#include <string.h> /* Get declaration of strerror() */
#include <pthread.h>

#define MAX_ERROR_LEN 256 /* Maximum length of string in per-thread
                           * buffer returned by strerror() */

static __thread char buf[MAX_ERROR_LEN]; /* Thread-local return buffer */

char *
strerror(int err)
{
  printf("strerror with thread local storage is running ...\n");

  if (err < 0 || err >= _sys_nerr || _sys_errlist[err] == NULL) {
    snprintf(buf, MAX_ERROR_LEN, "Unknown error %d", err);
  } else {
    strncpy(buf, _sys_errlist[err], MAX_ERROR_LEN - 1);
    buf[MAX_ERROR_LEN - 1] = '\0';    /* Ensure null termination */
  }
  return buf;
}
