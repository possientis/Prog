#include <stdio.h>

int main(int argc, char *argv[]) {

  int i;

  printf("There were %d arguments provided:\n", argc);

  for(i=0; i < argc; i++){

    printf("argument #%d\t-\t%s\n", i, argv[i]);

  }
}
