#include <limits.h>
#include <stdio.h>

int main()
{

  int x;

  x = INT_MAX;
  printf("INT_MAX = %d\n", x);  // 2147483647

  x= INT_MIN;
  printf("INT_MIN = %d\n", x);  // -2147483648

  x = -x;
  printf("-INT_MIN = %d\n", x); // -2147483648 !!!!

  return 0;
}



