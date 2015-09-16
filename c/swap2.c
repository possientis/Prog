#include<iostream>
#include<utility> // std::swap
#include<vector>  // std::vector

int main()
{
  int x=10, y=20;
  std::swap(x,y);

  std::vector<int> foo(4,x), bar(6,y);
  std::swap(foo,bar);

  std::cout << "foo cointains:";
  for(std::vector<int>::iterator it = foo.begin(); it != foo.end(); ++it)
    std::cout << ' ' << *it;
  std::cout << '\n';

  return 0;

}
