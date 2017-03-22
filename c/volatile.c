#include <stdio.h>


int main()
{
  volatile int x = 12;  // tell compiler to not to optimize away access

  // compiler may wrongly think nothing has happened to variable 

  return 0;
}
