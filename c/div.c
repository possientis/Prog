// gcc -O -Wall -fverbose-asm -S main.c
// to see generated assembly code

#include <stdio.h>


int main()
{
  int x = 122;
  printf("x/2 = %d\n", x>>1);
  printf("x/2 = %d\n", x/2);
  printf("x = %d\n", x);

  return 0;
}

