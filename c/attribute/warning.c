#include <stdio.h>

void foo() __attribute__ ((warning("This function should no longer be used")));


int main()
{
  foo();
  return 0;
}

void foo() 
{
  printf("warning foo is running...\n");
}

/*
warning.c: In function ‘main’:
warning.c:8:3: warning: call to ‘foo’ declared with attribute warning: This function should no longer be used
   foo();
      ^~~~~
*/

