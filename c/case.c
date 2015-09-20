#include<iostream>

int main(){

  int x = 5;
  int y = 0;

  switch(x){

    case 0:
      y = 0;
      break;
    case 1:
      y = 1;
      break;
    case 2:
      y =2;
      break;
    default:
      y = 5;
      break;
  }

  std::cout << y << std::endl;
}
