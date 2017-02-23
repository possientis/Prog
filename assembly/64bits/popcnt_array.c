#include <malloc.h>
#include <stdio.h>
#include <stdlib.h>

long popcnt_array(long *a, int size)
{
  int w,b;
  long word;
  long n;

  n=0;

  for(w = 0; w < size; w++)
  {
    word = a[w];
    n += word & 1;  // +1 if lsb is 1
    for(b = 1; b < 64; b++)
    {
      n += (word >> b) & 1;
    }
  }

  return n;
}


int main()
{
  int size = 100000;
  int total = 0;
  int i;

  long *array = (long *) malloc(size * sizeof(long));
  if(array == NULL)
  {
    fprintf(stderr, "Failed to allocate array\n");
    exit(-1);
  }

  for(i =0; i < size; i++)
  {
    array[i] = random();
  }

  for(i = 0; i < 500; ++i)
  {
    int count = popcnt_array(array, size);
    total += count;
  }


  printf("total = %d\n", total);

  free(array);

  return 0;
}








