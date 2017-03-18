#include <stdio.h>

// struct is given a name
struct point {
  int x, y;
};


// struct not given a name but typedef used instead
typedef struct { int x,y; } pair;

typedef struct _prod { int x,y; } prod;


struct rectangle {
  struct point top_left, bottom_right;
};


int main()
{
  struct point p = { .x = 1, .y = 2 };  // c99
  pair q = { x:3 , y:4 };               // gnu extension
  struct point r = {5,7};

  printf("p = (%d,%d)\n", p.x, p.y);
  printf("q = (%d,%d)\n", q.x, q.y);
  printf("r = (%d,%d)\n", r.x, r.y);

  struct rectangle R = { {0,5}, {10,0} }; // inner braces just for readability 
  printf("R.top_left     = (%d,%d)\n", R.top_left.x, R.top_left.y);
  printf("R.bottom_right = (%d,%d)\n", R.bottom_right.x, R.top_left.y);

  struct rectangle S = { 1, 4, 8, 1 };
  printf("S.top_left     = (%d,%d)\n", S.top_left.x, S.top_left.y);
  printf("S.bottom_right = (%d,%d)\n", S.bottom_right.x, R.top_left.y);

  return 0;
}
