#include <time.h>
#include <stdio.h>


int main(){
  
  time_t now = time(NULL);
  
  printf("The current date is: %s", ctime(&now));

  return 0;
}
