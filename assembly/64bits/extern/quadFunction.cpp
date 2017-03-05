#include <iostream>
#include <stdlib.h>

using namespace std;

extern "C" unsigned long 
quadFunction(
    int index,
    unsigned long x1, 
    unsigned long x2, 
    unsigned long x3, 
    unsigned long x4, 
    unsigned long x5, 
    unsigned long x6, 
    unsigned long x7, 
    unsigned long x8
)
{
  switch(index)
  {
    case 1: return x1;
    case 2: return x2;
    case 3: return x3;
    case 4: return x4;
    case 5: return x5;
    case 6: return x6;
    case 7: return x7;
    case 8: return x8;
    default: 
      cerr << "quadFunction: invalid index argument\n";
      exit(1);
  }
}
        

