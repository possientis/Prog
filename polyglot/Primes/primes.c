#include <stdio.h>
#include <malloc.h>
#include <assert.h>
#include <stdlib.h> // atoi

// message should have occurrence of '%lx' for function to work
static int memory_log(const char* message, void* ptr){
  static long memory_check = 0L;
  // simply retrieving checksum
  if(message == NULL && ptr == NULL) return memory_check;
  // genuine logging action
  assert(message != NULL);
  assert(ptr != NULL);
  fprintf(stderr, message, ptr);// expexting '%lx' in message to print address
  memory_check ^= (long) ptr;   // bitwise exclusive or
}


typedef struct Cell_ Cell;

typedef Cell* (*Thunk)(void);

struct Cell_ {
  int count;  // reference count
  int car;    // first component of cell, aka first, head
  Thunk cdr;  // second component of cell, aka rest, tail, may be NULL
  Cell* cache;// cached value of thunk, NULL if thunk has not been called
};

Cell* Cell_copy(Cell* self){
  assert(self != NULL);
  memory_log("Making copy of cell %lx\n", self);
  self->count++;
  return self;
}

Cell* Cell_new(int first, Thunk rest){
  Cell* ptr = (Cell*) malloc(sizeof(Cell));
  assert(ptr != NULL);
}








int main(int argc, char* argv[]){
  assert(argc == 2);  // a single argument expected
  int numPrimes = atoi(argv[1]);
 

  return 0;
}
