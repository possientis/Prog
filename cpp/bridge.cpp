#include <utility>
#include <iostream>
#include <assert.h>

// some non-value type heavy duty class 
class Base {
  Base(const Base&);            // not implemented
  Base& operator=(const Base&); // not implemented
  public:
  int a;
  ~Base(){}
  Base(int a){this->a = a;}
};


class A {
  private:
  struct _Base{  // object Base with an added counter
    int count;
    Base object;
    _Base(int a):object(a),count(0){}
  };
  _Base* _impl;
  void swap(A& rhs){std::swap<_Base*>(_impl,rhs._impl);};

  public:
  ~A(){std::cout << "~A() running ...\n"; _impl->count--; if(_impl->count == 0) delete _impl;}
  A(int a){std::cout << "A(int) running ...\n"; _impl = new _Base(a); _impl->count=1;}
  A(const A& rhs):_impl(rhs._impl){std::cout << "A(const A&) running ...\n"; _impl->count++;}
  A& operator=(const A& rhs){A temp(rhs); swap(temp);}
  //A(const A* rhs){std::cout << "A(const A*) running ...\n"; assert(rhs != nullptr); _impl=rhs->_impl; _impl->count++; delete rhs;}
  int get(){return _impl->object.a;}
  void set(int a){_impl->object.a = a;}
  int count(){return _impl->count;}


};




int main(){

  A a = 1;
  A b = 2;
  A c = 3;

  std::cout << "a = " << a.get() << " , count = " << a.count() << std::endl;
  std::cout << "b = " << b.get() << " , count = " << b.count() << std::endl;
  std::cout << "c = " << c.get() << " , count = " << c.count() << std::endl;

  b = c;
  c.set(5);


  std::cout << "b = " << b.get() << " , count = " << b.count() << std::endl;
  std::cout << "c = " << c.get() << " , count = " << c.count() << std::endl;
  return 0;
}
