#include<stdio.h>

int main()
{
  goto final;

  printf("This line should not appear\n");

final:

  printf("Exiting program\n");

  return 0;
}
