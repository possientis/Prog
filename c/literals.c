#include <stdio.h>

int main(){

  // suffixes like L or UL can alsobe applied

  int a = 0x2a;       // hexadecimal
  int b = 42;         // decimal
  int c = 052;        // octal
  int d = 0b101010;   // binary

  printf("a = %d; b = %d; c = %d; d = %d", a, b, c, d);

  return 0;
}
