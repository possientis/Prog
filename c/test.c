#include<stdio.h>
//#include<assert.h>
//#include<assert.h>
//#include<string.h>
//#include<malloc.h>
//#include<assert.h>


void f(int x){ printf("I am running: x = %d\n", x); }

void (*g(void (*h)(int)))(int){ return h; }

int main(int argc, char* argv[], char* envp[]){

  g(f)(3);

  return 0;
}


