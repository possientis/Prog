#include<stddef.h>
#include<stdio.h>

// local variables x and y contain the same data.
// however, compiler generated code differs based on type

int main()
{
  // unsigned long
  size_t x = 0xffffffffffffffffUL;

  printf("x = 0x%lx\n", x);

  if(x < 0) // x is unsigned value
  {
    printf("x is negative\n");
  }
  else
  {
    printf("x is positive\n");  // x is positive
  }

  // signed long
  long y = 0xffffffffffffffffUL;
  printf("y = 0x%lx\n", y);

  if(y < 0) // y is signed value
  { 
    printf("y is negative\n");  // y is negative
  }
  else
  {
   printf("y is positive\n");
  }

  printf("sizeof(size_t) = %d\n", sizeof(size_t)); 

  return 0;
}

