#include <iostream>

class A {
  public:
    virtual ~A(){ std::cout << "A::~A() running\n"; }
    virtual void foo(){ std::cout << "A::foo running\n"; }
    static void operator delete(void*){ std::cout << "not freeing pointer\n"; }
  private:
    int _a;
};

class B : public A {
  public:
    void foo() override { std::cout << "B::foo running\n"; }
  private:
    bool _whatever;
};


int main(){

  B* a = new B();
  a->foo();
  delete a; 
  delete a;
  delete a;


  return 0;

}


