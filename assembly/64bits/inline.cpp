#include <iostream>

using namespace std;


// inline assembly forces you to use AT&T syntax
int getValueFromASM()
{
  asm("movl $254, %eax");
}

// we avoid inline assembly and write function separately
// on another file, using Intel syntax and yasm
extern "C" int getValueFromYASM();

int main()
{
  cout << "ASM said " << getValueFromASM() << endl;
  cout << "YASM said " << getValueFromYASM() << endl;

  return 0;
}
