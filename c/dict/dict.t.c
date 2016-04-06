#include "dict.h"
#include <stdio.h>

int dictionary_test(){
  Dictionary* d;
  Dictionary* e;
  int errCode = 0;
  fprintf(stderr, "Dictionary: starting unit test\n");
  // new delete
  d = Dictionary_new(); 
  Dictionary_delete(d);
  if(Dictionary_hasMemoryLeak()){
    fprintf(stderr,"Dictionary: unit test 1.0 failing\n");
    errCode = -1;
  }
  // copy
  d = Dictionary_new(); 
  e = Dictionary_copy(d);
  Dictionary_delete(e); 
  Dictionary_delete(d); 
  if(Dictionary_hasMemoryLeak()){
    fprintf(stderr,"Dictionary: unit test 1.1 failing\n");
    errCode = -1;
  }

  fprintf(stderr, "Dictionary: unit test complete\n");  
  return errCode;
}


int main(){
  return dictionary_test();
}
