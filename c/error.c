#include <errno.h>
#include <string.h>
#include <stdio.h>

int main(int argc, char* argv[], char* envp[]){

  printf("Error message for %s is: %s\n", "EINVAL", strerror(EINVAL));
  printf("Error message for %s is: %s\n", "EFAULT", strerror(EFAULT));

  int i;
  for(i = 0; i < 134; ++i){
    printf("%s\n", strerror(i));
  }

  return 0;
}
