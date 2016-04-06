// getting file descriptor from a stream
// use fdopen to get stream from file descriptor
// file descriptors are useful for IO system calls (read write)
// streams are useful with the stdio library
// being able to convert one to the other is important
#include <stdio.h>


int main(){

  printf("fileno(stdin) = %d\n", fileno(stdin));
  printf("fileno(stdout) = %d\n", fileno(stdout));
  printf("fileno(stderr) = %d\n", fileno(stderr));

  return 0;
}
