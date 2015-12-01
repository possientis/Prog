#include "object.h"
#include <memory.h>
#include <stdio.h>
#include <assert.h>

void* func(struct op* self, void* args){


}
static int  test_op_init(){
  struct op oper;
  op_init(&oper, Cloneable_clone_func,NULL);
  if (op_run(&oper) != NULL){
    fprintf(stderr,"test_op_init failing\n");
    return -1;
  }
  return 0;
}

static int test(){
  if(test_op_init()) return -1;

  return 0;
}

int main(int argc, char* argv[]){

  return test();
}


