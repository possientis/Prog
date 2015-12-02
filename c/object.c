#include "object.h"
#include <memory.h>
#include <assert.h>
#include <stdio.h>
#include <malloc.h>

// main operation on a struct op structure
void* op_run(struct op* self){
  assert(self != NULL);
  return self->func(self, self->args);
};

// init
void op_init(struct op* self, void* (*func)(struct op*,void*), void* args){
  assert(self != NULL);
  self->func = func;
  self->args = args;
}

// alloc, size argument to allocate array
struct op* op_alloc(int size){
  assert(size > 0);
  struct op* ptr = (struct op*) malloc(size * sizeof(struct op));
  assert(ptr != NULL);
  return ptr;
}

// free, do not attempt to free individual element of array
void op_free(struct op* self){
  free((void*) self);
}


