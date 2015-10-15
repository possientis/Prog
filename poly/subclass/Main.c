// Main.c
#include "A.h"
#include "B.h"
#include <iostream>

int main(){
  A a(1);
  B b(2,3);
  std::cout << a.a << ":" << b.a << ":" << b.b << std::endl;
  a.foo();
  b.foo();
  B c(4,5);
  A* p = &c;
  p->foo();
  A a1 = a; // copy ctor
  B b1 = b; // copy ctor
  std::cout << a1.a << ":" << b1.a << ":" << b1.b << std::endl;

  A a2(2);
  A::swap(a1,a2);
  std::cout << a1.a << ":" << a2.a << std::endl;

  B::swap(b,c);
  std::cout << b.a << ":" << b.b << ":" << c.a << ":" << c.b << std::endl;


  return 0;
}

