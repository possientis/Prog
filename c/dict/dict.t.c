// dict.t.c
#ifndef INCLUDED_DICT
#include "dict.h"
#endif

#include <stdio.h>
#include <string>

static void printInt(const void* ptr){

  int i = *(int*) ptr;
  printf("%d",i);

}

static void printStr(const void* ptr){

  std::string s = *(std::string*) ptr;

  printf("%s",s.c_str());

}


static int dict_test();

int main(int argc, char* argv[]){

  return dict_test();

}

static int dict_test(){

  printf("Dictionary: starting unit test\n");

  int k1 = 1;
  int k2 = 2;
  int k3 = 3;
  int k4 = 4;

  int v1 = 10;
  int v2 = 20;
  int v3 = 30;
  int v4 = 40;

  const std::string s1 = "abc";
  const std::string s2 = "abc";

  int w1 = 100;
  int w2 = 200;


//  Dictionary<int> a;  // integer keys
  Dictionary<std::string> b;  // string keys

  // first insert
  //a.insert(k1,&v1);
  b.insert(s1,&w1);
  b.insert(s2,&w2);



  //a.debug(printInt,printInt);
  b.debug(printStr,printInt);

  printf("Dictionary: unit test complete\n");

  return 0;

}
