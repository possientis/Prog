#include <iostream>
#include <memory>

struct test
{
  test(){std::cout << "test::ctor" << std::endl;}
  ~test(){std::cout << "test::dtor" << std::endl;}
};

int main()
{
  std::unique_ptr<test[]> myptr(new test[3]);
}
