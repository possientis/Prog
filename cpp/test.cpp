#include<functional>

class myclass {
  private:
    std::function<int(int,int)> func;
  public:
    myclass(std::function<int(int,int)> func):func(func){}
    myclass(const myclass& other):func(other.func){}
    int operator()(int a,int b){return func(a,b);};
};

int main(){

  myclass a([](int i,int j){ return 2*i + j; });

  return 0;
}
