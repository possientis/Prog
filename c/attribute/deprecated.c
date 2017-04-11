#include <stdio.h>

void foo() __attribute__ ((deprecated));


int main()
{
  foo();
  return 0;
}

void foo() 
{
  printf("deprecated foo is running...\n");
}

/*
deprecated.c: In function ‘main’:
deprecated.c:8:3: warning: ‘foo’ is deprecated [-Wdeprecated-declarations]
   foo();
      ^~~
deprecated.c:3:6: note: declared here
   void foo() __attribute__ ((deprecated));
*/
