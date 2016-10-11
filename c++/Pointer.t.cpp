// Pointer.t.c
#include "Pointer.h"
#include <iostream>

class A {
  int a;
  public:
  A(int a){this->a = a;}
  int get() const {return a;}
};

int foo(const A& x){ return x.get();}

int main(){
  
  std::cout << "Pointer: starting unit test\n";
  // int
  Pointer<int> a(new int(100));
  Pointer<int> b(new int(200));
  if(a.count() != 1) std::cout << "Pointer: unit test 1.0 failing\n";
  if(b.count() != 1) std::cout << "Pointer: unit test 1.1 failing\n";
  if(*a != 100) std::cout << "Pointer: unit test 1.2 failing\n";
  if(*b != 200) std::cout << "Pointer: unit test 1.3 failing\n";
  Pointer<int> c(a);
  if(a.count() != 2) std::cout << "Pointer: unit test 1.4 failing\n";
  if(c.count() != 2) std::cout << "Pointer: unit test 1.5 failing\n";
  if(*a != 100) std::cout << "Pointer: unit test 1.6 failing\n";
  if(*c != 100) std::cout << "Pointer: unit test 1.7 failing\n";
  if(a.get() != c.get()) std::cout << "Pointer: unit test 1.8 failing\n";
  IPointer<int> *d = new Pointer<int>(a);
  if(a.count() != 3) std::cout << "Pointer: unit test 1.9 failing\n";
  if(**d !=100) std::cout << "Pointer: unit test 1.10 failing\n";
  delete d;
  if(a.count() != 2) std::cout << "Pointer: unit test 1.11 failing\n";
  c = b;
  if(a.count() != 1) std::cout << "Pointer: unit test 1.12 failing\n";
  if(b.count() != 2) std::cout << "Pointer: unit test 1.13 failing\n";
  if(c.count() != 2) std::cout << "Pointer: unit test 1.14 failing\n";
  if(*a != 100) std::cout << "Pointer: unit test 1.15 failing\n";
  if(*b != 200) std::cout << "Pointer: unit test 1.16 failing\n";
  if(*c != 200) std::cout << "Pointer: unit test 1.17 failing\n";
  if(b.get() != c.get()) std::cout << "Pointer: unit test 1.18 failing\n";
  a = b;
  if(a.count() != 3) std::cout << "Pointer: unit test 1.19 failing\n";
  if(b.count() != 3) std::cout << "Pointer: unit test 1.20 failing\n";
  if(c.count() != 3) std::cout << "Pointer: unit test 1.21 failing\n";
  if(*a != 200) std::cout << "Pointer: unit test 1.22 failing\n";
  if(*b != 200) std::cout << "Pointer: unit test 1.23 failing\n";
  if(*c != 200) std::cout << "Pointer: unit test 1.24 failing\n";
  if(b.get() != c.get()) std::cout << "Pointer: unit test 1.25 failing\n";
  if(b.get() != a.get()) std::cout << "Pointer: unit test 1.25 failing\n";
  // A
  Pointer<A> aA(new A(10));
  Pointer<A> bA(new A(20));
  if(aA.count() != 1) std::cout << "Pointer: unit test 2.0 failing\n";
  if(bA.count() != 1) std::cout << "Pointer: unit test 2.1 failing\n";
  if(foo(*aA) != 10) std::cout << "Pointer: unit test 2.2 failing\n";
  if(foo(*bA) != 20) std::cout << "Pointer: unit test 2.3 failing\n";
  if(aA->get() != 10) std::cout << "Pointer:unit test 2.4 failing\n";
  if(bA->get() != 20) std::cout << "Pointer::unit test 2.5 failing\n";
  Pointer<A> cA(aA);
  if(aA.count() != 2) std::cout << "Pointer: unit test 2.6 failing\n";
  if(cA.count() != 2) std::cout << "Pointer: unit test 2.7 failing\n";
  if(foo(*aA) != 10) std::cout << "Pointer: unit test 2.8 failing\n";
  if(foo(*cA) != 10) std::cout << "Pointer: unit test 2.9 failing\n";
  if(aA->get() != 10) std::cout << "Pointer:unit test 2.10 failing\n";
  if(cA->get() != 10) std::cout << "Pointer::unit test 2.11 failing\n";
  if(aA.get() != cA.get()) std::cout << "Pointer: unit test 2.12 failing\n";
  IPointer<A> *dA = new Pointer<A>(aA);
  if(aA.count() != 3) std::cout << "Pointer: unit test 2.13 failing\n";
  if(foo(**dA) != 10) std::cout << "Pointer: unit test 2.14 failing\n";
  if((*dA)->get() != 10) std::cout << "Pointer: unit test 2.15 failing\n";
  delete dA;
  if(aA.count() != 2) std::cout << "Pointer: unit test 2.16 failing\n";
  cA = bA;
  if(aA.count() != 1) std::cout << "Pointer: unit test 2.17 failing\n";
  if(bA.count() != 2) std::cout << "Pointer: unit test 2.18 failing\n";
  if(cA.count() != 2) std::cout << "Pointer: unit test 2.19 failing\n";
  if(foo(*aA) != 10) std::cout << "Pointer: unit test 2.20 failing\n";
  if(foo(*bA) != 20) std::cout << "Pointer: unit test 2.21 failing\n";
  if(foo(*cA) != 20) std::cout << "Pointer: unit test 2.22 failing\n";
  if(aA->get() != 10) std::cout << "Pointer: unit test 2.23 failing\n";
  if(bA->get() != 20) std::cout << "Pointer: unit test 2.24 failing\n";
  if(cA->get() != 20) std::cout << "Pointer: unit test 2.25 failing\n";
  if(bA.get() != cA.get()) std::cout << "Pointer: unit test 2.26 failing\n";
  aA = bA;
  if(aA.count() != 3) std::cout << "Pointer: unit test 2.27 failing\n";
  if(bA.count() != 3) std::cout << "Pointer: unit test 2.28 failing\n";
  if(cA.count() != 3) std::cout << "Pointer: unit test 2.29 failing\n";
  if(foo(*aA) != 20) std::cout << "Pointer: unit test 2.30 failing\n";
  if(foo(*bA) != 20) std::cout << "Pointer: unit test 2.31 failing\n";
  if(foo(*cA) != 20) std::cout << "Pointer: unit test 2.32 failing\n";
  if(aA->get() != 20) std::cout << "Pointer: unit test 2.33 failing\n";
  if(bA->get() != 20) std::cout << "Pointer: unit test 2.34 failing\n";
  if(cA->get() != 20) std::cout << "Pointer: unit test 2.35 failing\n";
  if(bA.get() != cA.get()) std::cout << "Pointer: unit test 2.36 failing\n";
  if(bA.get() != aA.get()) std::cout << "Pointer: unit test 2.37 failing\n";
 

  std::cout << "Pointer: unit test complete\n";
  return 0;
}
