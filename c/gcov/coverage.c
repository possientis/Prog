#include <stdio.h>

int main()
{

  int i,j;

  int x = 0;

  for(i = 0; i < 100; ++i){

    x += 50;

    for(j = 0; j < 100; ++j){

      x +=3;
    }
  }  

  printf("x = %d\n", x);

  return 0;

}
  
