#include <stdio.h>

void foo() __attribute__ ((deprecated));


int main()
{
  foo();
  return 0;
}

void foo() 
{
  printf("foo is running...\n");
}
