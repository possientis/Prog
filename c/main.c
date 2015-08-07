#include "pair.h"
#include<iostream>

int main()
{


  pair a(1,2);
  a.print();

  std::cout<< " ";

  a.set(3,4);
  a.print();

  std::cout<< "Attempting to access private data member " << a.d_x << "\n";

}
