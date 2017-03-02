#include <stdio.h>

// The program compiles and links whether or not
// debug() is defined in any object file.
#pragma weak debug

extern void debug(void);

void (*debugfunc)(void) = debug;

int main() {
      printf("Hello World!\n");
      if (debugfunc) (*debugfunc)();
}
