#include<stdio.h>


int main(int argc, char* argv[], char* envp[]){

  int x = 5;
  typeof(x) y = 6;

  printf("y = %d\n", y);

  return 0;
}


