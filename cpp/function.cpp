#include<functional>
#include<iostream>

static void scan(int* a, int length, std::function<void(int)> process)
{
  for(int i=0; i<length; i++) {
    process(a[i]);
  }
}

int main(){
  int a[10] = {0,1,2,3,4,5,6,7,8,9};

  scan(a, 10, [](int i) -> void {std::cout << i*i << " ";});

  return 0;

}
