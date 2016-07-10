#include <stdio.h>
#include <stdlib.h>
#include <malloc.h>
#include <assert.h>
#include <openssl/des.h> // gcc -lcrypto

int main(int argc, char* argv[]){


  /* does not seem to be needed ot useful
  time_t curtime = time(NULL);
  unsigned int iseed = (unsigned int) curtime;
  srand(iseed);
  */


  printf("size of random key is: %d\n", sizeof(DES_cblock));
  printf("size of long is: %d\n", sizeof(long));

  DES_cblock *key = (DES_cblock *) malloc(sizeof(DES_cblock));
  assert(key != NULL);
  printf("key memory location is %lx\n", key);

  *((long*) key) = 0L;


  long before = *((long *) key);
  printf("key prior to initialization: %lx\n", before);


  DES_random_key(key);  /* generating random key */

  long after = *((long*) key);
  printf("key after initialization: %lx\n", after);


  free(key);

  return 0;

}
