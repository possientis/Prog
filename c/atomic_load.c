#include <stdio.h>

int main()
{
  int i = 5;

  int j1 = __atomic_load_n(&i, __ATOMIC_SEQ_CST);
  int j2 = __atomic_load_n(&i, __ATOMIC_CONSUME);
  int j3 = __atomic_load_n(&i, __ATOMIC_ACQUIRE);
  int j4 = __atomic_load_n(&i, __ATOMIC_RELAXED);

  printf("j1 = %d\n", j1);
  printf("j2 = %d\n", j2);
  printf("j3 = %d\n", j3);
  printf("j4 = %d\n\n", j4);

  i = 6;

  __atomic_load(&i,&j1, __ATOMIC_SEQ_CST);
  __atomic_load(&i,&j2, __ATOMIC_CONSUME);
  __atomic_load(&i,&j3, __ATOMIC_ACQUIRE);
  __atomic_load(&i,&j4, __ATOMIC_RELAXED);

  printf("j1 = %d\n", j1);
  printf("j2 = %d\n", j2);
  printf("j3 = %d\n", j3);
  printf("j4 = %d\n\n", j4);

  return 0;
}
