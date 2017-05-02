#include <stdio.h>
#include <assert.h>

int main()
{
  int x,y;
  x = 2;
  __atomic_signal_fence(__ATOMIC_SEQ_CST);
  y = x;

  return 0;
}
