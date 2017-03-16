#include <stdio.h>

void foo(char x){}
void bar(signed char y){}
void baz(unsigned char z){}

int main(){

  // are these really distinct types?
  char a = 'A';
  signed char b = 'B';
  unsigned char c = 'C';


  a = b;
  b = c;
  c = a;

  foo(b); 
  foo(c);
  bar(a);
  bar(c);
  baz(a);
  baz(b);
  


  return 0;
}
