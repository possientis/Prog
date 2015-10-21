// Main.c
#include "A.h"
#include "B.h"
#include <iostream>

int main(){
  A a(1);
  B b(2,3);
  std::cout << a.aGet() << ":" << b.aGet() << ":" << b.bGet() << std::endl;
  a.foo();
  b.foo();
  B c(4,5);
  A* p = &c; p->foo();
  A a1 = a; // copy ctor
  B b1 = b; // copy ctor
  std::cout << a1.aGet() << ":" << b1.aGet() << ":" << b1.bGet() << std::endl;

  A a2(2);
  A::swap(a1,a2);
  std::cout << a1.aGet() << ":" << a2.aGet() << std::endl;

  B b2(4,5);
  B::swap(b1,b2);
  std::cout << b1.aGet() << ":" << b1.bGet() << ":" << b2.aGet() << ":" << b2.bGet() << std::endl;


  return 0;
}

