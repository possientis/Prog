#include <stdio.h>
#include <stddef.h>

int main()
{
  wchar_t c = 0xfeff;
  
  printf("sizeof(c) = %d\n", sizeof(c));


  return 0;
}
