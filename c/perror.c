#include <stdlib.h> // EXIT_FAILURE
#include <stdio.h>
#include <errno.h>  // errno
#include <string.h> // strerror

int main(){

  int fd = open("/filedoesnotexists",NULL,NULL);
  if(fd == -1){
    perror("my message indicating failure");  // will add message corresponding to errno
    // strerror will compile without including string.h, but code will produce segmentation fault
    printf("Error message from errno is: %s\n", strerror(errno));
    exit(EXIT_FAILURE);
  }

  // unlikely
  return 0;
}
