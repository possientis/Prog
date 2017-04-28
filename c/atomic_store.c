#include <stdio.h>

int main()
{
  int j1,j2,j3;

  __atomic_store_n(&j1, 7, __ATOMIC_SEQ_CST);
  __atomic_store_n(&j2, 7, __ATOMIC_RELEASE);
  __atomic_store_n(&j3, 7, __ATOMIC_RELAXED);

  printf("j1 = %d\n", j1);
  printf("j2 = %d\n", j2);
  printf("j3 = %d\n\n", j3);

  int i = 8;

  __atomic_store(&j1, &i, __ATOMIC_SEQ_CST);
  __atomic_store(&j2, &i, __ATOMIC_RELEASE);
  __atomic_store(&j3, &i, __ATOMIC_RELAXED);

  printf("j1 = %d\n", j1);
  printf("j2 = %d\n", j2);
  printf("j3 = %d\n\n", j3);

  return 0;
}
