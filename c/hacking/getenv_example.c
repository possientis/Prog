#include <stdio.h>
#include <stdlib.h>

int main(int argc, char *argv[]) {

  long i;  // not far from current stack pointer

  printf("variable i is at %14p\n", &i);
  printf("%s is at %14p\n", argv[1], getenv(argv[1]));

  i = (long) getenv(argv[1]) - (long) &i;

  printf("difference is %ld\n", i);

}
