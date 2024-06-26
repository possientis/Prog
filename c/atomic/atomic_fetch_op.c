#include <stdio.h>
#include <assert.h>


int main()
{

  int n1, n2, n3;

  // temp = n1; n1 += n2; return temp;
  n1 = 1; n2 = 2; n3 = 6;
  n3 = __atomic_fetch_add(&n1, n2, __ATOMIC_SEQ_CST);
  assert(n1 == 3); assert(n2 == 2); assert(n3 == 1);

  // temp = n1; n1 -= n2; return temp;
  n1 = 1; n2 = 2; n3 = 6;
  n3 = __atomic_fetch_sub(&n1, n2, __ATOMIC_SEQ_CST);
  assert(n1 == -1); assert(n2 == 2); assert(n3 == 1);


  return 0;
}
