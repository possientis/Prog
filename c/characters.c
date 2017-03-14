#include <stdio.h>

int main()
{
  // character constants of type intby default
  const int list[14] = { 
    '\\', '\?', '\'', '\"', '\a', '\b', '\e' /* GNU*/, '\f',
    '\n', '\r', '\t', '\v','\101', '\x41'
  }; 

  int i;

  for(i = 0; i < 14; ++i){
    printf("%d: %d\n", i, list[i]);
  }

  return 0;
}
