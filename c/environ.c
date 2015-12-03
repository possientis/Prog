#include <stdio.h>
#include <memory.h>

extern void* environ; // global variable of the C library

int main(int argc, char* argv[], char* envp[])
{


  int i=0;

  while(envp[i] != NULL){
    printf("envp[%d] = %s\n",i,envp[i]);
    ++i;
  }

  printf("environ=%lx\n",environ);
  printf("envp=%lx\n",envp);

  return 0;
}
