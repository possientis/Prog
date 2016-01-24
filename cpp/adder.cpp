#include<functional>
#include<iostream>


std::function<int(int)> adder(int x){

  // replacing [x] by [&x] does not produce expected behaviour
  return [x](int y){return x + y;};

}



int main(){

  std::function<int(int)> add5 = adder(5);
  auto add10 = adder(10);

  std::cout << "5 + 7 = " << add5(7) << std::endl;
  std::cout << "10 + 2 = " << add10(2) << std::endl;

  int x = 3;
  auto addx = adder(x);

  std::cout << "6 + x = " << addx(6) << std::endl;

  x++;  // would expected this to matter when using [&x]

  // output does change when using [&x], but does produce expected result
  // output does not change when capture by value '[x]' despite x++
  std::cout << "6 + x = " << addx(6) << std::endl;

  return 0;
}
