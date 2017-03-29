#include <stdio.h>

int main()
{

  float x;

  int y = 7;
  int z = 3;

  x = (float) (y / z);  /* keep (..) around expression too */

  printf("x = %f\n", x);  // 2.00000

  x = y / (float) z;

  printf("x = %f\n", x);  // 2.33333

  /* casting only works for integer, floating point or pointer types */

  return 0;
}


