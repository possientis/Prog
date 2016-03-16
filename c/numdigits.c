#include <stdio.h>


// function for returning number of digits 
int main(){

  int length = snprintf(0,0,"%d",188989);
  printf("length = %d\n", length);

  return 0;
}
