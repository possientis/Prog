#include <stdio.h>


int main()
{
  int (*p)[4][12];
  int (*q)[4][30];

  p = q;



  printf("Hello world!\n");
  return 0;
}
