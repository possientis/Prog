#include <stdio.h>

void foo() __attribute__ ((error("This function should no longer be used")));


int main()
{
  foo();
  return 0;
}

void foo() 
{
  printf("error foo is running...\n");
}

/*
error.c: In function ‘main’:
error.c:8:3: error: call to ‘foo’ declared with attribute error: This function should no longer be used
   foo();
      ^~~~~
*/
