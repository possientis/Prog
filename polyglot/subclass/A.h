#ifndef A_INCLUDED
#define A_INCLUDED

#include <iostream>
#include <assert.h>

class A{

  // needs to be private
  int a;
  A(const A&);  // not implemented, implementing A(const A*) below

  public:
  A(int a){this->a = a;}
  A(const A* rhs){std::cout<< "running\n"; assert(rhs!=nullptr); a = rhs->a;} // closer to Java
  int aGet(){return this->a;}
  void aSet(int a){this->a = a;}
  virtual void foo(){ std::cout << "A::foo() is running\n";}
  virtual ~A(){}  // always need virtual dtor

  // no throw swap procedure
  // could be non-member, went for static instead
  // to keep parallelism with Java and C#
  static void swap(A* x,A* y){
  std::swap(x->a,y->a);
  }

 };

#endif
