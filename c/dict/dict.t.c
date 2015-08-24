// dict.t.c
#ifndef INCLUDED_DICT
#include "dict.h"
#endif

#include <stdio.h>
#include <string.h>

// comparison operator for integer keys
static int comp1(const void* x, const void* y){

  int u = *(int*) x;
  int v = *(int*) y;
  return (u - v);

}

// comparison operator for string keys
static int comp2(const void* x, const void* y){

  const char* u = (const char*) x;
  const char* v = (const char*) y;

  return strcmp(u,v);

}

int dict_test();

int main(int argc, char* argv[]){

  return dict_test();

}

int dict_test(){

  printf("Dictionary: starting unit test\n");

  Dictionary a(comp1);  // integer keys
  Dictionary b(comp2);  // string keys

  printf("Dictionary: unit test complete\n");

  return 0;

}
