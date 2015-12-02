#include <stdio.h>
#include <memory.h>


int main(int argc, char* argv[], char* envp[])
{


  int i=0;

  while(envp[i] != NULL){
    printf("envp[%d] = %s\n",i,envp[i]);
    ++i;
  }

  return 0;
}
