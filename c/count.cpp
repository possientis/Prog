#include <iostream>
#define STOP 0

int main()
{
  int counter;
  int startPoint;

  std::cout<< "===== Countdown Program =====\n";
  std::cout<< "Enter a positive integer: ";
  std::cin>>startPoint;

  for (counter = startPoint; counter >=STOP; counter--)
    std::cout<<counter<<'\n';
}
