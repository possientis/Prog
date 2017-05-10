#include <stdio.h>
#include <assert.h>

int main()
{
  volatile int x, y;
  x = 2;
  __atomic_thread_fence(__ATOMIC_SEQ_CST);
  y = x;

  return 0;
}
