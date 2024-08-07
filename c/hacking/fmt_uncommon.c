#include <stdio.h>
#include <stdlib.h>

int main() {
  int A = 5, B = 7, count_one, count_two;
  
  // Example of a %n format string
  printf(
      "The number of bytes written up to this point X%n is being stored in "
      "count_one, and the number of bytes up to here X%n is being stored in "
      "count_two.\n", &count_one, &count_two
  );
  
  printf("count_one: %d\n", count_one);
  printf("count_two: %d\n", count_two);
  
  // Stack example
  printf("A is %d and is at %14p. B is %x.\n", A, &A, B);

  exit(0);
}
