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
  int threshold = 5;
  int max = 0;

  scan(a, 10, [](int i) -> void {std::cout << i*i << " ";});
  std::cout << std::endl;
  scan(a,10,[threshold](int i) -> void {if(threshold <= i) std::cout << i << " ";});
  std::cout << std::endl;
  scan(a,10,[=](int i) -> void {if(threshold <= i) std::cout << 3*i << " ";});  // '=' shortcut
  std::cout << std::endl;
  scan(a,10,[threshold,&max](int i) -> void {if ((i >= threshold) && (i >= max)) max = i;});
  std::cout << "max = " << max << std::endl;
  max = 0;
  scan(a,10,[&](int i) -> void {if ((i >= threshold) && (i*i >= max)) max = i*i;}); // every variable captured by ref
  std::cout << "max = " << max << std::endl;
  return 0;

}
