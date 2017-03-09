#include <stdio.h>

#include <iso646.h>
/*
 * and
 * and_eq
 * bitand
 * bitor
 * compl
 * not
 * not_eq
 * or
 * or_eq
 * xor
 * xor_eq
 */

#define X 1
#define Y 1

int main()
{
# if X and Y
  printf("X and Y is true\n");
# else
  printf("X and Y is false\n");
# endif

  if(X and Y) // cpp expands 'and' as '&&'
  {
    printf("X and Y is really true\n");
  }
  else
  {
    printf("X and Y are not so true\n");
  }

  return 0;
}

