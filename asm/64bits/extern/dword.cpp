// c++ source code which calls an assembly function
// which itself calls a c++ function.

#include <iostream>
#include <assert.h>

using namespace std;

#define INT(n) 0x##n##n##n##n##n##n##n##n##U

// This is the prototype of the assembly function called in this source
// simply returns argument of given index 1-8

extern "C" unsigned int 
dwordASMFunction(
    int index, 
    unsigned int x1, 
    unsigned int x2, 
    unsigned int x3, 
    unsigned int x4, 
    unsigned int x5, 
    unsigned int x6, 
    unsigned int x7, 
    unsigned int x8
);


int main()
{
  unsigned int x[] = {
    INT(1),     // 0x11111111U
    INT(2),     // 0x22222222U
    INT(3),     // 0x33333333U
    INT(4),     // 0x44444444U
    INT(5),     // 0x55555555U
    INT(6),     // 0x66666666U
    INT(7),     // 0x77777777U
    INT(8)      // 0x88888888U
  };

  cout << "\nAssembly function call from C++ with ints ...\n";

  for(int i = 0; i < 8; ++i) 
  {
    cout << "x" << i + 1 << " = 0x" << hex << x[i] << endl;

    // checking the call to assembly function is succesful
    // This implicitely validates the call of the assembly 
    // function to the c++ function.

    assert(x[i] == dwordASMFunction(i+1,x[0],x[1],x[2],x[3],x[4],x[5],x[6],x[7]));
  }

  return 0;
}
