#ifndef A_INCLUDED
#define A_INCLUDED

#include <iostream>

class A{

  // needs to be private
  int a;

  public:
  A(int a){this->a = a;}
  A(const A& rhs){a = rhs.a;}
  int aGet(){return this->a;}
  void aSet(int a){this->a = a;}
  virtual void foo(){ std::cout << "A::foo() is running\n";}
  virtual ~A(){}  // always need virtual dtor

  // no throw swap procedure
  // could be non-member, went for static instead
  // to keep parallelism with Java and C#
  static void swap(A& x,A& y){
  std::swap(x.a,y.a);
  }

 };

#endif
