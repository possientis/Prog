// genereric to_string, toString in C++

#include <sstream>
#include <iostream>

template<typename T>
std::string toString(T t){
  std::ostringstream s; // stringstream seems to work too

  s << t;
  return s.str();
}


int main(){
  int x = 42;
  std::string y = "abc";
  bool z = false;
  double pi = 3.13159;

  std::cout << toString(x) << std::endl;
  std::cout << toString(y) << std::endl;
  std::cout << toString(z) << std::endl;
  std::cout << toString(pi) << std::endl;

  return EXIT_SUCCESS;
}
