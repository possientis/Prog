#include <stdlib.h>
#include <stdio.h>

static int intcompare(const void *p1, const void *p2)
{
  int i = *((int *)p1);
  int j = *((int *)p2);
  return (i - j) ;
}

int main()
{
  int i;
  int a[10] = { 9, 8, 7, 6, 5, 4, 3, 2, 1, 0 };
  qsort((void *)a, 10, sizeof (int), intcompare);
  for (i = 0; i < 10; ++i) { printf("%d ", a[i]); }
  printf("\n");
  return 0;
}
