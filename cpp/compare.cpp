#include <iostream>

class compare {
  private:
    int l,r;
  public:
    compare(int i, int j):l(i),r(j){}
    bool operator()(){ return l < r; }
    operator bool(){ return l < r; }
};


int main(){

  std::cout << compare(2,5)() << std::endl;
  std::cout << compare(2,5) << std::endl;

  auto comp = [](int i, int j){ return i < j; };

  std::cout << comp(3,6) << std::endl;

  return 0;
}
