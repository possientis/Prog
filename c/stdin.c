#include <unistd.h>
#include <stdio.h>
#define MAX_READ 31



int main(){
  char buffer[MAX_READ+1];
  ssize_t numRead;

  numRead = read(STDIN_FILENO, buffer, MAX_READ);
  if(numRead == -1)
    return -1;

  buffer[numRead] = '\0';

  printf("The input data was: %s\n", buffer);


  return 0;
}
