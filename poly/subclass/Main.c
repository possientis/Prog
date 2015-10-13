// Main.c
#include "A.h"
#include "B.h"
#include <iostream>

int main(){
  A a(1);
  B b(2,3);
  std::cout << a.a << ":" << b.a << ":" << b.b << std::endl;;
  a.foo();
  b.foo();

  B c(4,5);
  A* p = &c;
  c.foo();

  return 0;
}

