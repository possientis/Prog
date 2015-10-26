// Main.c
#include "A.h"
#include "B.h"
#include <iostream>

int main(){
  // Attempting to follow java
  A* a = new A(1);  // following java, but need to deal with pointer
  B* b = new B(2,3);
  std::cout << a->aGet() << ":" << b->aGet() << ":" << b->bGet() << std::endl;
  a->foo();
  b->foo();
  A* c = new B(4,5);
  c->foo();
  A* a1 = new A(a); // copy ctor A(const A*) allowing cleaner syntax here
  B* b1 = new B(b); // copy ctor B(const B*) allowing cleaner syntax here
  std::cout << a1->aGet() << ":" << b1->aGet() << ":" << b1->bGet() << std::endl;

  A* a2 = new A(2);
  A::swap(a1,a2); // swap(A*,A*) allowing cleaner syntax here
  std::cout << a1->aGet() << ":" << a2->aGet() << std::endl;

  B* b2 = new B(4,5);
  B::swap(b1,b2); // swap(B*,B*) allowing cleaner syntax here
  std::cout << b1->aGet() << ":" << b1->bGet() << ":" << b2->aGet() << ":" << b2->bGet() << std::endl;

  delete a; // no garbage collection
  delete b;
  delete c;
  delete a1;
  delete b1;
  delete a2;
  delete b2;

  //don't understand why compiler attempts to use A(const A&)
  //A d = new A(10); // automatic d created from copy A(const *A)
  //std::cout << d.aGet() << std::endl;
  // but memory of temp object A(10) never released

  return 0;
}

