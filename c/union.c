#include <stdio.h>

union numbers {
  int i;
  float f;
};


int main()
{

  printf("size of union numbers = %d\n", sizeof(union numbers));

  union numbers x;
  union numbers y;
  x.i = 45;
  y.f = 4.5;

  union numbers z = {5};  // first union member only
  union numbers t = { f: 3.14159 };
  union numbers u = { .f = 6.28318 };


  printf("z = %d\n", z.i);
  printf("t = %f\n", t.f);
  printf("u = %f\n", u.f);

  return 0;
}
