#include <stdio.h>
#include <stdlib.h>


unsigned int 
dwordFunction(
    int index,
    unsigned int x1, 
    unsigned int x2, 
    unsigned int x3, 
    unsigned int x4, 
    unsigned int x5, 
    unsigned int x6, 
    unsigned int x7, 
    unsigned int x8
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
      fprintf(stderr, "dwordFunction: invalid index argument\n");
      exit(1);
  }
}
        
            
