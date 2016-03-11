#include <stdio.h>
#include <malloc.h>
#include <assert.h>
#include <stdlib.h> // atoi

typedef struct Cell_ Cell;
typedef struct Func_ Func;

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

/******************************************************************************/
/*                                Func  Class                                 */
/******************************************************************************/

struct Func_ {
  int   count;                            // reference counter
  void* data;                             // data
  void* (*func)(void* data, void* args);  // code
};

Func* Func_copy(Func* self){
  assert(self != NULL);
  memory_log("Making copy of functional %lx\n", self);
  self->count++;
  return self;
}

Func* Func_new(void* data, void* (*func)(void*,void*)){
  Func* ptr = (Func*) malloc(sizeof(Func));
  assert(ptr != NULL);
  memory_log("Allocating new functional %lx\n", ptr);
  ptr->count = 1;
  ptr->data = data;
  ptr->func = func;
  return ptr;
}

void* Func_delete(Func* self){
  assert(self != NULL);
  assert(self->count > 0);
  self->count--;                // decreasing reference count;
  if(self->count == 0){         // memory deallocation needs to take place
    self->data    = NULL;
    self->func    = NULL;
    memory_log("Deallocating existing functional %lx\n", self);
    free(self);
  }
  else{                         // reference count was decreased. Done.
    memory_log("Deleting copy of functional %lx\n", self);
  }
}

void* Func_call(Func* self, void* args){
  assert(self != NULL);
  return self->func(self->data, args);
}

// code for the function pointer required to initialize
// a thunk which returns a given Cell* (given as data)
// when called with no argument
void* Func_init_wrapper(void* data, void* args){
  return (Cell*) data;
}




/******************************************************************************/
/*                                 Cell Class                                 */
/******************************************************************************/


struct Cell_ {
  int count;  // reference count
  int car;    // first component of cell, aka first, head
  Func* cdr;  // second component of cell, aka rest, tail, may be NULL
  Cell* cache;// cached value of thunk, NULL if thunk has not been called
};

Cell* Cell_copy(Cell* self){
  assert(self != NULL);
  memory_log("Making copy of cell %lx\n", self);
  self->count++;
  return self;
}

Cell* Cell_new(int first, Func* rest){
  Cell* ptr = (Cell*) malloc(sizeof(Cell));
  assert(ptr != NULL);  // rest can be NULL
  memory_log("Allocating new cell %lx\n", ptr);
  ptr->count = 1;
  ptr->car = first;
  ptr->cdr = rest;
  ptr->cache = NULL;
  return ptr;
}

void Cell_delete(Cell* self){
  assert(self != NULL);
  assert(self->count > 0);
  self->count--;                // decreasing reference count;
  if(self->count == 0){         // memory deallocation needs to take place
    if(self->cache != NULL){    // allocated cell is linked to self
      Cell_delete(self->cache); // recursive call
    }
    self->car   = 0;
    self->cdr   = NULL;
    self->cache = NULL;
    memory_log("Deallocating existing cell %lx\n", self);
    free(self);
  }
  else{                         // reference count was decreased. Done.
    memory_log("Deleting copy of cell %lx\n", self);
  }
}

int Cell_first(Cell* self){
  assert(self != NULL);
  return self->car;
}

Cell* Cell_rest(Cell* self){
  assert(self != NULL);
  if(self->cache != NULL){ 
    return self->cache;
  }
  if(self->cdr == NULL){      // thunk is null
    return NULL;
  }
  self->cache = (Cell*) Func_call(self->cdr,NULL);
  self->cdr = NULL;          // no need to keep pointer

  return self->cache;        // no copy, caller has sole ownership
} 


Cell* Cell_cons(int first, Cell* rest){
  Func* func = Func_new(rest, Func_init_wrapper);
  return Cell_new(first, func);
} 



int main(int argc, char* argv[]){
  assert(argc == 2);  // a single argument expected
  int numPrimes = atoi(argv[1]);

  Cell* x = Cell_new(2,NULL);
  Cell* y = Cell_cons(3,x);

  printf("x.first = %d\n", Cell_first(x));
  printf("x.rest  = %lx\n", Cell_rest(x));
  printf("y.first = %d\n", Cell_first(y));
  printf("y.rest.first = %d\n", Cell_first(Cell_rest(y)));
  printf("y.rest.rest = %d\n", Cell_rest(Cell_rest(y)));



  Cell_delete(y);
  Cell_delete(x);

  long checkSum = memory_log(NULL,NULL);
  if(checkSum != 0){
    fprintf(stderr, "Memory leak was detected\n");
    return -1;
  }

  return 0;
}
