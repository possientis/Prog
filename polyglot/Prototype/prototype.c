// Prototype design pattern
// Imagine that in order to instantiate certain objects we need to carry out
// expensive database queries. In order to improve performance, it would 
// be beneficial to cache whatever object is created from the database
// and return a copy of the cached object whenever a subsequent request
// for object instantiation arises.
#include "object.h"
#include <memory.h>
#include <stdio.h>
#include <assert.h>

static void* Cloneable_clone_func(struct op* self, void* args){
  assert(self != NULL);   // no reason to call otherwise
  fprintf(stderr,"Cloneable::clone is not implemented\n");
  return NULL;
}


int main(int argc, char* argv[]){

  test();

  return 0;
}


