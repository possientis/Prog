#include <stdio.h>
#include <stdlib.h>

int main(int argc, char* argv[]){

  printf("argc = %d\n", argc);
  int i;
  for(i = 0; i < argc; ++i){
    printf("argv[%d] = %s\n",i, argv[i]);
  }

  
  time_t curtime = time(NULL);
  printf("current time is: %ld\n", (long) curtime);


  unsigned int iseed = (unsigned int) curtime;
  srand(iseed);


  printf("RAND_MAX = %d\n", (long) RAND_MAX);
  printf("rand = %d\n", rand());
  printf("rand = %d\n", rand());
  printf("rand = %d\n", rand());

  return 0;

}
