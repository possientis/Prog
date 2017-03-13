#include <stdio.h>

#define eprintf1(...) fprintf(stderr, __VA_ARGS__)  // first syntax
#define eprintf2(args...) fprintf(stderr, args)      // syntax with named arguments
//
// possible but less flexible, as you need at least one optional argument here
#define eprintf3(format,...) fprintf(stderr, format, __VA_ARGS__)
#define eprintf4(format, args...) fprintf(stderr, format, args)


int main()
{
  eprintf1("%s\n", "Hello World!");
  eprintf2("%s\n", "Hello World!");
  eprintf3("%s\n", "Hello World!");
  eprintf4("%s\n", "Hello World!");
//  eprintf3("Hello World!\n");     // syntax error
//  eprintf4("Hello World!\n");     // syntax error

  return 0;
}
