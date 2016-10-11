#include<iostream>

class Base {
  public:
    virtual void foo(){std::cout << "running base foo()\n";}

};


class Derived : public Base {

  public:
  //void foo() override;

};



int main()
{
  Derived b;
  std::cout << "calling foo() on derived object...\n";
  b.foo();
}


// void Derived::foo(){std::cout << "running derived foo()\n";}
