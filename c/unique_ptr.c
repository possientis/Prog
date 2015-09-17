#include <iostream>
#include <memory>

struct test
{
  test(){std::cout << "test::ctor" << std::endl;}
  ~test(){std::cout << "test::dtor" << std::endl;}
};

int main()
{
  std::cout << "size = " << sizeof(test) << std::endl;
  std::unique_ptr<test[]> myptr(new test[3]);
}
