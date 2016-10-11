#include<functional>
#include<iostream>


std::function<int(int)> adder(int &x){


  // using [&x] here will not work unless x is passed to adder 
  // by reference. Otherwise, [&x] will simply capture the reference
  // of a local copy of x, which will defeat the purpose of [&x] v [x]
  return [&x](int y){return x + y;};  // [x] or [&x]

}


int main(){

  int x = 3;
  auto addx = adder(x);

  std::cout << "6 + x = " << addx(6) << std::endl;

  x++;  // would expected this to matter when using [&x]

  std::cout << "6 + x = " << addx(6) << std::endl;

  return 0;
}
