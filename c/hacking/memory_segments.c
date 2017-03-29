#include <stdio.h>
#include <malloc.h>

int global_var;

int global_initialized_var = 5;

void function() { // This is just a demo function.
  int stack_var = 89;  // Notice this variable has the same name as the one in main().
  printf("the function's stack_var is at address %14p\n", &stack_var);
}

int main() {

  int stack_var; // Same name as the variable in function()

  static int static_initialized_var = 5;
  
  static int static_var;

  int *heap_var_ptr;
  heap_var_ptr = (int *) malloc(4);

  // These variables are in the data segment.
  printf(".data segment:\n");
  printf("global_initialized_var is at address %14p\n", &global_initialized_var);
  printf("static_initialized_var is at address %14p\n\n", &static_initialized_var);
  // These variables are in the bss segment.
  printf(".bss segment:\n");
  printf("static_var is at address %14p\n", &static_var);
  printf("global_var is at address %14p\n\n", &global_var);
  // This variable is in the heap segment.
  printf("heap segment:\n");
  printf("*heap_var_ptr (the value) is at address %14p\n\n", heap_var_ptr);
  // These variables are in the stack segment.
  printf("stack segment:\n");
  printf("stack_var is at address %14p\n", &stack_var);
  function();
  printf("heap_var_ptr (the pointer) is at address %14p\n", &heap_var_ptr);
}
