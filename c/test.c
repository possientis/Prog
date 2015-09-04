#include<stdio.h>
#include<string>  //std::string
//#include<string.h>
//#include<malloc.h>
//#include<assert.h>
//#include<iostream>




int main()
{

  std::string s1 = "abc";
  std::string s2 = "def";
  std::string s3 = "abc";

  printf("%lx\n",&s1);
  printf("%lx\n",&s2);
  printf("%lx\n",&s3);
  printf("%d\n",sizeof(std::string));

  if(s1 == s2){
    printf("s1 == s2 is true\n");
  }
  else
  {
    printf("s1 == s2 is false\n");
  }

  if(s1 == s3){
    printf("s1 == s3 is true\n");
  }
  else
  {
    printf("s1 == s3 is false\n");
  }

  return 0;


}

