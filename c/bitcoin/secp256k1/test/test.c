#include "test.h"
#include <stdio.h>
#include <assert.h>

void default_callback(const char* message, void* data){
  fprintf(stderr, "callback function is rightly called: %s\n", message);
  *((int*) data) = 42;
}

int is_all_null(const void *ptr, size_t size)
{
  assert(ptr != NULL);
  assert(size >= 0);

  const unsigned char *p = ptr;

  size_t i;
  for(i = 0; i < size; ++i)
  {
    if( *p++ != '\x00' ) return 0;
  }

  return 1;
}




