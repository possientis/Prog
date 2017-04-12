#include<stdio.h>

// weak symbols are useful in defining library functions
// which can be overriden in user code

// creates weak symbol
#pragma weak foo  

// creates a weak symbol
void baz() __attribute__((weak));

// creates and define a weak symbol
void __attribute__((weak)) bar() { printf("default bar version is running\n"); }

// definition
void foo() { printf("default foo version is running\n");}

// definition
void baz() { printf("default baz version is running\n"); }

int main(int argc, char* argv[], char* envp[]){

  foo();
  bar();
  baz();

  return 0;
}


