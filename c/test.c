#include<stdio.h>
#include<iostream>
//#include<string.h>
#include<malloc.h>
#include<assert.h>

int main(int argc, char * argv[])
{

  using namespace std;

  long e;
  int a;
  int b;
  short c;
  short d;
  char f;
  long g;

  cout << "One long, two int, two short and one char" << endl;

  cout << hex << &e << endl << &a << endl << &b << endl << &c << endl << &d << endl;
  cout << hex << (void*) &f << endl << &g << endl;


  return 0;


}
