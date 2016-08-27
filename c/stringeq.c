#include<stdio.h>
//#include<string.h>
//#include<malloc.h>
//#include<assert.h>




int main()
{

  const char * s1 = "hello";
  const char * s2 = "hello";

  if((void*) s1 == (void*) s2){
    printf("yes, equal\n");
  }
  else
  {
    printf("no, not equal\n");
  }

  return 0;


}

