#include <stdio.h>
#include <stdlib.h>

int main(){

  char *s = getenv("HOSTNAME");

  if(s == NULL)
    printf("s is NULL\n");
  else
    printf("%s\n", getenv("HOSTNAME"));

  return 0;
}
