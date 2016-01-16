#include <stdio.h>

int main(int argc, char* argv[], char* envp){

  int i = 0;

  if((2 == 2) || (++i));  // do nothing

  printf("i = %d\n", i);   // expecting i = 0

  if((2 == 3) && (++i));

  printf("i = %d\n", i);

  return 0;
}
