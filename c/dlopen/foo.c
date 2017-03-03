#include <stdio.h>

void __attribute__ ((constructor)) my_lib_start()
{
  printf("libfoo.so is being loaded\n");
}

void __attribute__ ((destructor)) my_lib_exit()
{
  printf("libfoo.so is being unloaded\n");
}



void foo()
{
  printf("foo is running ...\n");
}
