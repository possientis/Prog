#include <stdio.h>

long fact(long x) {

  if(x <= 1) return 1;
  
  return fact(x - 1) * x;
}

int main() {

  long x;

  scanf("%ld", &x);

  printf("fact(%ld) = %ld\n", x, fact(x));

  return 0;
}
