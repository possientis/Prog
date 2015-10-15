#ifndef B_INCLUDED
#define B_INCLUDED

#include "A.h"

class B : public A{
  public:
  int b;
  B(int a, int b) : A(a){this->b = b;}
  B(const B& rhs) : A(rhs){b = rhs.b;}
  void foo() override {std::cout << "B::foo() is running\n";}

  // no throw swap procedure
  // could be non-member, went for static instead
  // to keep peralelism with Java and C#
  static void swap(B& x, B& y) {
    A::swap(x,y);
    std::swap(x.b,y.b);
  }

 };

#endif

