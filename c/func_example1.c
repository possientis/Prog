#include<stdio.h>
//#include<assert.h>
//#include<assert.h>
//#include<string.h>
//#include<malloc.h>
//#include<assert.h>

// It is possible to write C function which
// return function pointers

// simple function
void f(int x){ printf("I am running: x = %d\n", x); }

// function returning a void (*)(int) and 
// taking a void (*)(int) as argument
void ( *g1( void (*h)(int) )  )(int){ return h; }

// of course, such definition is not very readable. Instead:


typedef void (*sighandler_t)(int);

sighandler_t g2(sighandler_t h){ return h; /* or whatever */ }





int main(int argc, char* argv[], char* envp[]){

  g1(f)(3); // I am running: x = 3
  g2(f)(5); // I am running: x = 5

  return 0;
}


