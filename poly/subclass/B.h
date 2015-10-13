#ifndef B_INCLUDED
#define B_INCLUDED

#include "A.h"

class B : public A{
  public:
  int b;
  B(int a, int b) : A(a){this->b = b;}
  void foo() override {std::cout << "B::foo() is running\n";}
};

#endif

