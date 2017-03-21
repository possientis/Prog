#include <stdio.h>

typedef struct { long x; } some_type;

typedef struct point incomplete_type;

int main()
{

  some_type*  p1;
  some_type * p2;
  some_type  *p3;

  some_type *p, *q;     // two pointers
  some_type *r, X;      // one pointer and a variable

  some_type *s = &X;    // initialize with address

//  incomplete_type a;  // cannot
  incomplete_type *a;   // that's fine, useful for linked list

  return 0;
}
