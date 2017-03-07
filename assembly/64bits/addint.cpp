#include <iostream>

using namespace std;

int addInts(int a, int b, int c, int d)
{
  asm("movq %rdi, %rax");
  asm("addq %rsi, %rax");
  asm("addq %rdx, %rax");
  asm("addq %rcx, %rax");
}

int main()
{

  cout << "result = " << addInts(12,3,6,-7) << endl;

  return 0;
}
