#include<stdio.h>
//#include<assert.h>
//#include<string.h>
//#include<malloc.h>


int main(int argc, char* argv[], char* envp[]){

  printf("size1 = %d\n", sizeof(size_t)); 
  printf("size2 = %d\n", sizeof(ssize_t));
  printf("size3 = %d\n", sizeof(long));
  printf("size4 = %d\n", sizeof(long long));

  return 0;
}


