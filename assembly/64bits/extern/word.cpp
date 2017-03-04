// c++ source code which calls an assembly function
// which itself calls a c++ function.

#include <iostream>
#include <assert.h>

using namespace std;

#define SHORT(n) 0x##n##n##n##n##U

// This is the prototype of the assembly function called in this source
// simply returns argument of given index 1-8

extern "C" unsigned short 
shortASMFunction(
    int index, 
    unsigned short x1, 
    unsigned short x2, 
    unsigned short x3, 
    unsigned short x4, 
    unsigned short x5, 
    unsigned short x6, 
    unsigned short x7, 
    unsigned short x8
);


int main()
{
  unsigned short x[] = {
    SHORT(1),     // 0x1111U
    SHORT(2),     // 0x2222U
    SHORT(3),     // 0x3333U
    SHORT(4),     // 0x4444U
    SHORT(5),     // 0x5555U
    SHORT(6),     // 0x6666U
    SHORT(7),     // 0x7777U
    SHORT(8)      // 0x8888U
  };

  cout << "\nAssembly function call from C++ with shorts ...\n";

  for(int i = 0; i < 8; ++i) 
  {
    cout << "x" << i + 1 << " = 0x" << hex << x[i] << endl;

    // checking the call to assembly function is succesful
    // This implicitely validates the call of the assembly 
    // function to the c++ function.

    assert(x[i] == shortASMFunction(i+1,x[0],x[1],x[2],x[3],x[4],x[5],x[6],x[7]));
  }

  return 0;
}
