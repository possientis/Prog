#include <stdio.h>

#ifdef __cplusplus
#define LANGUAGE "C++"
#else
#define LANGUAGE "C"
#endif

int main(){

  printf("We are running some %s code\n", LANGUAGE);

  return 0;
}
