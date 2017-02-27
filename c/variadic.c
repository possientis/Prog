#include <stdarg.h> // varargs.h has been deprecated
#include <stdio.h>

// https://en.wikipedia.org/wiki/Variadic_function

// passing number of variable arguments 'count' is possible idiom
// but not at all enforced by the language
double average(int count, ...)
{
  va_list ap; // variable arguments list

  int j;
  double sum = 0;

  // initialize variable arguments list
  va_start(ap, count); // Requires the last parameter before ellipsis '...'

  for (j = 0; j < count; j++) {
    // scan variable arguments list
    sum += va_arg(ap, int); /* Increments ap to the next argument. */
  }
  // clean up
  va_end(ap);

  return sum / count;
}

int main(int argc, char const *argv[])
{
    printf("average(1, 2, 3) = %f\n", average(3, 1, 2, 3) );
    printf("average(1, 2, 3, 4, 0) = %f\n", average(5, 1, 2, 3, 4, 0) );
    return 0;
}

