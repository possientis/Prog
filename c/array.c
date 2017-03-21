#include <stdio.h>
#include <malloc.h>

typedef struct {
  long x,y;
} some_type;

int main()
{

  some_type my_array[10];
  some_type *my_pointer = my_array;

  some_type zero[0];  // gnu extension


  int int_array[5] = { 0, 1, 2, 3, 4};
  int int_other[5] = { 0, 1, 2};          // last 2 elements initialized to 0
  int int_again[5] = { [2] 5, [4] 9};     // C99 or C89 + gnu extensions
  int int_sigh[5]  = { [2] = 5, [4] = 9 };
  int int_well[5]  = { 0, 0, 5, 0, 9 };
  int int_new[100] = { [0 ... 9] = 1, [10 ... 98] = 2, 3 };
  int int_hello[]  = { 1, 2, 3, 4, 5};
  int int_var[]    = { 1, 2, 3, [99] = 23 };

  some_type my_var[2] = { {4,5} , {7,8} };

  int two_dimension[2][5] = { {1,2,3,4,5}, {11,12,13,14,15} };
  int three_dim[2][5][3] = { \
    {{1,1,1},{2,2,2},{3,3,3},{4,4,4},{5,5,5}} , \
    {{2,2,2},{6,6,6},{7,7,7},{8,8,8},{9,9,9}} };

  printf("size of some_type   = %d\n", sizeof(some_type));  // 16
  printf("size of my_array    = %d\n", sizeof(my_array));   // 160
  printf("size of my_pointer  = %d\n", sizeof(my_pointer)); // 8
  printf("size of zero        = %d\n", sizeof(zero));       // 0
  printf("size of int_hello   = %d\n", sizeof(int_hello));  // 20
  printf("size of int_var     = %d\n", sizeof(int_var));    // 400


  // string arrays
  char blue[26];
  unsigned char yellow[26];
  const char red[] = "If const, you probabaly need to initialize";
  char white[] = { 'a', 'b', 'c' }; 
  char orange[] = "abc";
  char *green   = "abc";
  //  This fails however without cast
  char *pink    = (char[]) { 'a', 'b', 'c' };


  return 0;
}

void function(int number){

  some_type var[number];    // dynamic stack allocation

}
