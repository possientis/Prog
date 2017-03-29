#include <stdio.h>
#include <stddef.h>

static const int values[] = {1, 2, 48, 681 };

/* This does not work for 0 size or when array is function parameter */
#define ARRAYSIZE(x) (sizeof (x)/sizeof (x)[0])

int main()
{
  size_t i;

  for(i = 0; i < ARRAYSIZE(values); ++i)
  {
    printf("value[%d] = %d\n", i, values[i]);
  }

  return 0;
}
