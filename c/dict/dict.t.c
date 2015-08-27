// dict.t.c
#ifndef INCLUDED_DICT
#include "dict.h"
#endif

#include <stdio.h>
#include <string>

template <class K>
size_t prehash(const K& key);


int dict_test();

int main(int argc, char* argv[]){

  return dict_test();

}

int dict_test(){

  printf("Dictionary: starting unit test\n");

  Dictionary<int> a;  // integer keys
  Dictionary<std::string> b;  // string keys


  printf("Dictionary: unit test complete\n");

  return 0;

}
