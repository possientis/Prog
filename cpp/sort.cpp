#include <algorithm>
#include <iostream>

class comp{
  public:
  comp(){std::cout << "comp object is being instantiated\n";}
  bool operator()(int i, int j){ return i < j; }
  bool operator()(int k){return true;}  // you can overload the stuff
};

int main()
{
  int a[10] = { 9, 8, 7, 6, 5, 4, 3, 2, 1, 0 };
  int b[10] = { 9, 8, 7, 6, 5, 4, 3, 2, 1, 0 };

  std::sort(a,&a[10],[](int x, int y){ return x < y; } );
  for(int i=0; i<10; i++){
    std::cout << a[i] << " ";
  }
  std::cout << std::endl;

  comp x;

  std::sort(b,&b[10], x);
  for(int i=0; i<10; i++){
    std::cout << b[i] << " ";
  }
  std::cout << std::endl;

  std::cout << x(2,5) << std::endl;




  return 0;
}
