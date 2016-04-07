// link.t.c
#include "link.h"
#include <stdio.h>
#include <assert.h>
#include <malloc.h>


int Link_test(){

  int errCode = 0;

  fprintf(stderr, "Link: starting unit test\n");
  Link* a = Link_new();
  Link* b = Link_copy(a);
  Link_delete(b);
  Link_delete(a);

  fprintf(stderr, "Link: unit test complete\n");
 
  // checking for memory leaks
  if(Link_hasMemoryLeak()){
    fprintf(stderr, "Link: memory leak detected\n");
    errCode = -1;
  }


  return errCode;
}

int main(){
  return Link_test();
}


