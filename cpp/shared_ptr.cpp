#include <iostream>
#include <memory>
// shared pointers used for T[] (arrays)
struct test
{
  test(){std::cout << "test::ctor" << std::endl;}
  ~test(){std::cout << "test::dtor" << std::endl;}
};

int main()
{
  // <test> and not <test[]>
  std::shared_ptr<test> myptr(new test[3],std::default_delete<test[]>());
  //std::shared_ptr<test> myptr(new test[3]); // fails badly on destruction
  //won't compile
  //std::shared_ptr<test[]> myptr(new test[3],std::default_delete<test[]>());
  // won't compile
  // std::shared_ptr<test[]> myptr(new test[3]);
}
