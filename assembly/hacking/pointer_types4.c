#include <stdio.h>

int main() {

  int i;

  char char_array[5] = {'a', 'b', 'c', 'd', 'e'};
  int int_array[5] = {1, 2, 3, 4, 5};

  typedef unsigned long HackyPointer; /* works without 'unsigned' */

  HackyPointer hacky_pointer;

  hacky_pointer = (HackyPointer) int_array;
  for(i=0; i < 5; i++) { // Iterate through the int array with the void_pointer.

    printf("[integer pointer] points to %018p, which contains the integer %d\n",
        hacky_pointer, *((int *) hacky_pointer));

    hacky_pointer = hacky_pointer + sizeof(int);
  }

  hacky_pointer = (HackyPointer) char_array;
  for(i=0; i < 5; i++) { // Iterate through the char array with the void_pointer.

    printf("[char pointer] points to %018p, which contains the char '%c'\n",
        hacky_pointer, *((char *) hacky_pointer));

    hacky_pointer = hacky_pointer + sizeof(char);
  }

}
