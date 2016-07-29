#include <stdio.h>

int main(){

  unsigned long a = 1UL << 32;   // compiler warning, good
  unsigned long b = 1UL << 32;  

  printf("%lu %lu\n",a,b);

  printf("%d\n", sizeof(1U));   // 4
  printf("%d\n", sizeof(1UL));  // 8

  return 0;
}
