#include <stdio.h>

int main()
{
  char  w = '1';
  int   x = 5;
  char  y = 'B';
  float z = 5.2;
  int  *p = &x;


  printf("w = %c\n", ++w);  // '2'
  printf("x = %d\n", ++x);  // 6
  printf("y = %c\n", ++y);  // C
  printf("z = %f\n", ++z);  // 6.2
  printf("p               = 0x%014x\n", p++);
  printf("p + sizeof(int) = 0x%014x\n", p);

  return 0;
}


