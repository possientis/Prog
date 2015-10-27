#include <iostream>
#include <assert.h>

class Base {
  Base(const Base&);            // not implemented
  Base& operator=(const Base&); // not implemented
  public:
  int a;
  ~Base(){}
  Base(int a){this->a = a;}
};

class A {

  struct pBase{
    int count;
    Base obj;
    pBase(int a):obj(a),count(0){}
  };

  pBase* _impl;
  A& operator=(const A&);   // not implemented

  A(const A&){std::cout << "ctor running\n";}
  public:
  ~A(){std::cout << "~A() running ...\n"; _impl->count--; if(_impl->count == 0) delete _impl;}
  A(int a){std::cout << "A(int) running ...\n"; _impl = new pBase(a); _impl->count=1;}
//  A(const A& rhs):_impl(rhs._impl){std::cout << "A(const A&) running ...\n"; _impl->count++;}
  int get(){return _impl->obj.a;}
  int count(){return _impl->count;}
};




int main(){

  A c = 2;

  std::cout << "c = " << c.get() << " , count = " << c.count() << std::endl;
  
  return 0;
}
