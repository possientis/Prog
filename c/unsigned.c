#include <stdio.h>

int main()
{
  unsigned int x;
  int y = -1;

  x = y;      // compiler is not bothered

  if(x == y)  // compiler is not bothered
  {
    printf("x and y are equal\n");
  }
  else
  {
    printf("x and y are different\n");
  }

  printf("x = %u\n", x);
  printf("x = %d\n", x);

  /*
   * x and y are equal
   * x = 4294967295
   * x = -1
   */

  char c = -1;
  printf("c = %u\n", c);
  printf("c = %d\n", c);
  printf("c = %c\n", c);

  if(c == x)
  {
    printf("x and c are equal\n");
  }
  else
  {
    printf("x and c are different\n");
  }

  /*
   * c = 4294967295
   * c = -1
   * c = �
   * x and c are equal
   */

 

  return 0;
}
