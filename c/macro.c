#include <stdio.h>

// #EXP is stringification of argument

#define WARN_IF(EXP) \
  do { if(EXP) \
          fprintf(stderr, "Warning: " #EXP "\n"); } \
  while(0)

// ok but syntactically odd (missing ';')
#define WARN_IF_AGAIN(EXP) \
  if(EXP) \
    fprintf(stderr, "Warning again: " #EXP "\n")

// ok but usage is odd
#define WARN_IF_YET_AGAIN(EXP) \
  if(EXP) \
    fprintf(stderr, "Warning yet again: " #EXP "\n");



int main()
{
  int i = 0;
  int j = 1;

  WARN_IF(i == 0);
  WARN_IF(j == 0);
  
  WARN_IF_AGAIN(i == 0);
  WARN_IF_AGAIN(j == 0);


  WARN_IF_YET_AGAIN(i == 0) // odd syntax
  WARN_IF_YET_AGAIN(j == 0) // odd syntax

  return 0;
}


