#include <stdint.h>
#include <stdio.h>
#include <inttypes.h>
#include <string.h>
#include <wchar.h>

#define SIZE (8*1024)
unsigned char zero[SIZE] __attribute__(( aligned(8) ));

#define RDTSC(var) __asm__ __volatile__ ( "rdtsc" : "=A" (var) );

// benchmarking
#define MEASURE( func ) { \
  uint64_t start, stop; \
  RDTSC( start ); \
  int ret = func( zero, SIZE); \
  RDTSC( stop ); \
  printf( #func ": %s    %12"PRIu64"\n", ret?"non-zero":"zero", stop-start); \
}


int func1(unsigned char *buff, size_t size){
  while(size--) if(*buff++) return 1;
  return 0;
}

int func2(unsigned char *buff, size_t size){
  return *buff || memcmp(buff, buff+1, size-1);
}

int func3(unsigned char *buff, size_t size){
  return *(uint64_t*)buff || memcmp(buff, buff+8, size-8);
}

int func4(unsigned char *buff, size_t size){
  return *(wchar_t*)buff || 
         wmemcmp((wchar_t*)buff, (wchar_t*)buff+1,size/sizeof(wchar_t) -1);
}


int main(){

  MEASURE( func1 );
  MEASURE( func2 );
  MEASURE( func3 );
  MEASURE( func4 );



  return 0;
}
