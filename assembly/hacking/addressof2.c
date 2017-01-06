#include <stdio.h>

int main() {

  int int_var = 5;
  int *int_ptr;
  int_ptr = &int_var; // Put the address of int_var into int_ptr.

  printf("int_ptr = %018p\n", int_ptr);
  printf("&int_ptr = %018p\n", &int_ptr);
  printf("*int_ptr = %d\n\n", *int_ptr);
  printf("int_var is located at %018p and contains %d\n", &int_var, int_var);
  printf("int_ptr is located at %018p, contains %018p, and points to %d\n\n",
      &int_ptr, int_ptr, *int_ptr);
}
