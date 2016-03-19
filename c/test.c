#include<stdio.h>
//#include<assert.h>
//#include<assert.h>
//#include<string.h>
#include<malloc.h>
//#include<assert.h>


int main(int argc, char* argv[], char* envp[]){

  int* p;
  void* q;

  p = malloc(10*sizeof(int));

  q = p;

  free(p);

  return 0;
}


