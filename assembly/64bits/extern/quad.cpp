// c++ source code which calls an assembly function
// which itself calls a c++ function.

#include <iostream>
#include <assert.h>

using namespace std;

#define LONG(n) 0x##n##n##n##n##n##n##n##n##n##n##n##n##n##n##n##n##UL

// This is the prototype of the assembly function called in this source
// simply returns argument of given index 1-8

extern "C" unsigned long 
longASMFunction(
    int index, 
    unsigned long x1, 
    unsigned long x2, 
    unsigned long x3, 
    unsigned long x4, 
    unsigned long x5, 
    unsigned long x6, 
    unsigned long x7, 
    unsigned long x8
);


int main()
{
  unsigned long x[] = {
    LONG(1),    // 0x1111111111111111UL
    LONG(2),    // 0x2222222222222222UL
    LONG(3),    // 0x3333333333333333UL
    LONG(4),    // 0x4444444444444444UL
    LONG(5),    // 0x5555555555555555UL
    LONG(6),    // 0x6666666666666666UL
    LONG(7),    // 0x7777777777777777UL
    LONG(8)     // 0x8888888888888888UL
  };

  cout << "\nAssembly function call from C++ with longs ...\n";

  for(int i = 0; i < 8; ++i) 
  {
    cout << "x" << i + 1 << " = 0x" << hex << x[i] << endl;

    // checking the call to assembly function is succesful
    // This implicitely validates the call of the assembly 
    // function to the c++ function.

    assert(x[i] == longASMFunction(i+1,x[0],x[1],x[2],x[3],x[4],x[5],x[6],x[7]));
  }

  return 0;
}



