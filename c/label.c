#include <stdio.h>

int main()
{

  void* label_ptr = &&error;  // '&&' is a gnu extension

  goto *label_ptr;

  return 0;


error:
  printf("This is not really an error...\n");

  return 0;

}
