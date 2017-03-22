#include <stdio.h>

void foo()
{
  // storage class auto (default) (on the stack)
  auto int x = 4;
  printf("x = %d\n", x);
}

void bar()
{
  // storage class register (in a register)
  register int x = 5;
  printf("x = %d\n", x);
}

void baz()
{
  // static storage (.data section, keeps value between calls)
  static int x = 6;
  printf("x = %d\n", x);
  x++;
}


int main()
{
  foo();
  bar();
  baz();
  baz();
  return 0;
}


