#include<stdio.h>

#pragma weak foo  
/* only included by linker if not already defined */
void foo() { printf("default foo version is running\n");}

int main(int argc, char* argv[], char* envp[]){

  foo();
}


