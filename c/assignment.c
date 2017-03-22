#include <stdio.h>

typedef struct { int x, y; } some_type;


int main()
{

  some_type a = { 2, 3};

  some_type b;

//  b = { 2, 3};  // cannot

  return 0;
}
