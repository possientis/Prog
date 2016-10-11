#include<stdio.h>
#include<iostream>
//#include<string.h>
#include<malloc.h>
#include<assert.h>

int main(int argc, char * argv[])
{

  using namespace std;

  const char* friends[] = {"Al", "Bob", "Carl"};

  cout << "First pointer is " << &friends[0] << endl;
  cout << "Second pointer is " << &friends[1] << endl;
  cout << "Third pointer is " << &friends[2] << endl;

  char* p = (char*) friends;

  unsigned long a = *(unsigned long*) p;

  cout << hex << a << endl;

  char* q = (char*) a;

  printf("string is %s\n",q);
  printf("string is %s\n",q+3);
  printf("string is %s\n",q+7);

  for(int i = 0; i < 24; i++){

    //cout <<  (int) *p << endl;
    printf("%x:", (int) *p);
    p++;
  }

  return 0;


}
