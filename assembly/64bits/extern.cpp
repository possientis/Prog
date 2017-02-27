#include <iostream>

using namespace std;

extern "C" long longASMFunction
(
 long x1,
 long x2,
 long x3,
 long x4,
 long x5,
 long x6
 );

int main()
{

  long x1 = 0x1111111111111111L;
  long x2 = 0x2222222222222222L;
  long x3 = 0x3333333333333333L;
  long x4 = 0x4444444444444444L;
  long x5 = 0x5555555555555555L;
  long x6 = 0x6666666666666666L;

  long res = longASMFunction(x1, x2, x3, x4, x5, x6);

  cout << hex << "Result = 0x" << res << endl;
  
  return 0;
}
