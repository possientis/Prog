#include<stdio.h>
//#include<assert.h>
//#include<assert.h>
//#include<string.h>
//#include<malloc.h>
//#include<assert.h>

enum color { red, blue, green };

void foo(enum color c){
  printf("checking type safety\n");
}
int main()
{
  foo(red);
  foo(0); // bad boy
  return 0;
}


