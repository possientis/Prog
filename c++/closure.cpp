#include <iostream>
#include <functional>
#include <string>

int main(){

  std::string message = "hello";
  int value = 45;

  std::function<void(void)> example = [&message](){ // '[message]' or '[&message]'
    std::cout << message << std::endl;
  };

  std::function<int(int)> adder = [&value](int x){ // '[value]' or '[&value]'
    return value + x;
  };

  example();
  message = "changing message";
  example();

  std::cout << adder(10) << std::endl;
  value += 1;
  std::cout << adder(10) << std::endl;


  return 0;
}
