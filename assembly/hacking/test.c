#include <stdio.h>

void f(unsigned int x){
  printf("x = %x\n", x);
}

int main()
{

  int a = -5;

  f(a);

  return 0;
}
