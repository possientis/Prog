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

const unsigned char *pubkey_bytes1 = "\x03"
  "\xf0\x28\x89\x2b\xad\x7e\xd5\x7d\x2f\xb5\x7b\xf3\x30\x81\xd5\xcf"
  "\xcf\x6f\x9e\xd3\xd3\xd7\xf1\x59\xc2\xe2\xff\xf5\x79\xdc\x34\x1a";


