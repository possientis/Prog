#include <stdio.h>

void function() { // An example function, with its own context

  int var = 5;
  static int static_var = 5; // Static variable initialization

  printf("\t[in function] var @ %14p = %d\n", &var, var);
  printf("\t[in function] static_var @ %14p = %d\n", &static_var, static_var);

  var++;        // Add one to var.
  static_var++; // Add one to static_var.

}

int main() { // The main function, with its own context

  int i;
  static int static_var = 1337; // Another static, in a different context

  for(i=0; i < 5; i++) {        // Loop 5 times.

    printf("[in main] static_var @ %14p = %d\n", &static_var, static_var);
    function(); // Call the function.
  }

}
