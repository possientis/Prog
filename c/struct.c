#include<stdio.h>

struct Pair {

  int x;
  int y;

};


int main()
{
  struct Pair p = {.x = 1, .y=2};

  printf("x = %d, y = %d\n", p.x, p.y);

  return 0;
}
