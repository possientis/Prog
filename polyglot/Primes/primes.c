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
  void* (*code)(void* data, void* args);  // code
  void  (*delete)(Func* self);            // virtual destructor
};

// generic boiler-plate code for copy
Func* Func_copy(Func* self){
  assert(self != NULL);
  memory_log("Making copy of functional %lx\n", self);
  self->count++;
  return self;
}

// generic boiler-plate code for heap allocation
Func* Func_new(
    void* data,                           // virtual destructor will know
    void* (*code)(void*,void*),           // static data, no issue of ownership
    void  (*delete)(Func* self)           // static data, no issue of ownership
){
  Func* ptr = (Func*) malloc(sizeof(Func));
  assert(ptr != NULL);
  memory_log("Allocating new functional %lx\n", ptr);
  ptr->count = 1;
  ptr->data = data; // cannot tell here whether Func has sole ownership of data
  ptr->code = code;
  ptr->delete = delete;
  return ptr; // caller has sole ownership of object, no 'copy'
}

// generic boiler-plate code for destruction, virtual deallocation
void* Func_delete(Func* self){
  assert(self != NULL);
  assert(self->count > 0);
  self->count--;                // decreasing reference count;
  if(self->count == 0){         // memory deallocation needs to take place
    void(*delete)(Func*);     
    delete = self->delete;
    delete(self);               // calling virtual destructor
  }
  else{                         // reference count was decreased. Done.
    memory_log("Deleting copy of functional %lx\n", self);
  }
}

// Func object encapsulates data and code, and gives us a 'call' method
void* Func_call(Func* self, void* args){
  assert(self != NULL);
  return self->code(self->data, args);
}

/******************************************************************************/
/*                               () -> value                                  */
/******************************************************************************/

// Given a value of type Cell*, we need to instantiate a Func object which
// represents the lambda expression () -> value. This is the simplest case.
// The Func object requires three elements, data, code and destructor.

Cell* Cell_copy(Cell* self);  // forward

// caller shares ownership of Cell with Func, as copy is made
void* Lambda_Wrapper_code(void* data, void* args){
  return Cell_copy((Cell*) data);
}

void Cell_delete(Cell* self); // forward

void Lambda_Wrapper_delete(Func* self){
  assert(self != NULL);
  assert(self->count == 0);
  Cell* cell = (Cell*) self->data;  // data of wrapper lambda is Cell*
  Cell_delete(cell);
  self->data    = NULL;
  self->code    = NULL;
  self->delete  = NULL;
  memory_log("Deallocating functional %lx\n", self);
  free(self);
}

// Func has sole ownership of Cell, while caller has ownership of Func 
Func* Lambda_Wrapper_new(Cell* value){
  return Func_new(value, Lambda_Wrapper_code, Lambda_Wrapper_delete);
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

// generic boiler-plate code for copy 
Cell* Cell_copy(Cell* self){
  assert(self != NULL);
  memory_log("Making copy of cell %lx\n", self);
  self->count++;
  return self;
}

// generic boiler-plate code for heap allocation
Cell* Cell_new(int first, Func* rest){
  Cell* ptr = (Cell*) malloc(sizeof(Cell));
  assert(ptr != NULL);  // rest can be NULL
  memory_log("Allocating new cell %lx\n", ptr);
  ptr->count = 1;
  ptr->car = first;
  ptr->cdr = rest;  // Cell has sole ownership of Func, no 'copy'
  ptr->cache = NULL;
  return ptr;
}

void Cell_delete(Cell* self){
  assert(self != NULL);
  assert(self->count > 0);
  self->count--;                // decreasing reference count;
  if(self->count == 0){         // memory deallocation needs to take place
    self->car   = 0;
    if(self->cache != NULL){    // allocated cell is linked to self
      Cell_delete(self->cache); // recursive call
      self->cache = NULL;
    }
    if(self->cdr != NULL){
      Func_delete(self->cdr);
      self->cdr   = NULL;
    }
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

// Warning: does not return a copy. If you need to retain ownership, make copy
Cell* Cell_rest(Cell* self){
  assert(self != NULL);
  if(self->cache != NULL){ 
    return self->cache;              
  }
  if(self->cdr == NULL){            // thunk is null
    return NULL;
  }
  self->cache = (Cell*) Func_call(self->cdr,NULL); // getting full ownership
  Func_delete(self->cdr);           // no need to keep thunk 
  self->cdr = NULL;                 // no need to keep pointer

  return self->cache;    
} 

Cell* Cell_cons(int first, Cell* rest){
  Func* func;
  if(rest != NULL){
    func = Lambda_Wrapper_new(rest);  // Func takes full owenership of Cell
  }
  else{
    func = NULL;
  }
  return Cell_new(first, func);           // Cell has full ownership of Func
} 



/******************************************************************************/
/*                      () -> fromTransition(init,transition)                 */
/******************************************************************************/

// Given a transition function transition: int->int, and a initial value x:int
// we need be able to represent the lambda () -> fromTransition(x,transition)
// where fromTransition is defined below returns a Cell*. The data encapsulated
// is essentially an integer together with the transition function:

typedef struct Transition_ Transition;
struct Transition_ {
  int init;
  int (*transition)(int);
};


// The Func object representing lambda expression requires data
void* Lambda_Transition_data(int init, int (*transition)(int)){
  assert(transition != NULL);
  Transition* data = (Transition* ) malloc(sizeof(Transition));
  assert(data != NULL);
  memory_log("Allocating transition data %lx\n", data);
  data->init = init;
  data->transition = transition;
  return (void*) data;
}

Cell* Cell_fromTransition(int init, int (*transition)(int));  // forward
// The Func object representing lambda expression requires code
void* Lambda_Transition_code(void* data, void* args){
  assert(data != NULL);
  Transition* trans = (Transition*) data;
  int init = trans->init;
  int (*transition)(int);
  transition = trans->transition;
  return Cell_fromTransition(init, transition);
}

// The Func object representing lambda expression requires destructor
void Lambda_Transition_delete(Func* self){
  assert(self != NULL);
  assert(self->count == 0);
  Transition* trans = (Transition*) self->data;  
  memory_log("Deallocating transition data %lx\n", trans);
  free(trans);
  self->data    = NULL;
  self->code    = NULL;
  self->delete  = NULL;
  memory_log("Deallocating functional %lx\n", self);
  free(self);
}

Func* Lambda_Transition_new(int init, int (*transition)(int)){
  return Func_new(
      Lambda_Transition_data(init, transition),
      Lambda_Transition_code,
      Lambda_Transition_delete
  );
}

Cell* Cell_fromTransition(int init, int (*transition)(int)){
  assert(transition != NULL);
  Func* func = Lambda_Transition_new(transition(init), transition);
  assert(func != NULL);
  return Cell_new(init,func);
}


/******************************************************************************/
/*                      () -> this.rest().take(N)                             */
/******************************************************************************/

// As part of the recursive implementation of Cell_take, we need to represent
// the lambda expression () -> this.rest().take(N-1). The encapsulated data
// is essentially an integer and a pointer 'this'.

typedef struct TakeData_ TakeData;
struct TakeData_ {
  int value;
  Cell* cell;
};


// The Func object representing lambda expression requires data
void* Lambda_Take_data(int value, Cell* cell){
  assert(cell != NULL);
  TakeData* data = (TakeData*) malloc(sizeof(TakeData));
  assert(data != NULL);
  memory_log("Allocating take data %lx\n", data);
  data->value = value;
  data->cell = cell;    // Func object takes full ownership
  return (void*) data;
}

Cell* Cell_take(Cell*, int); // forward

// The Func object representing lambda expression requires code
void* Lambda_Take_code(void* data, void* args){
  assert(data != NULL);
  TakeData* take = (TakeData*) data;
  int value = take->value;
  Cell* cell = take->cell;
  return Cell_take(Cell_rest(cell), value);
}

// The Func object representing lambda expression requires destructor
void Lambda_Take_delete(Func* self){
  assert(self != NULL);
  assert(self->count == 0);
  TakeData* take = (TakeData*) self->data;  
  memory_log("Deallocating take data %lx\n", take);
  free(take);
  self->data    = NULL;
  self->code    = NULL;
  self->delete  = NULL;
  memory_log("Deallocating functional %lx\n", self);
  free(self);
}

Func* Lambda_Take_new(int value, Cell* cell){
  return Func_new(
      Lambda_Take_data(value, cell),
      Lambda_Take_code,
      Lambda_Take_delete
  );
}

Cell* Cell_take(Cell* self, int N){
  assert(self != NULL);
  assert(N > 0);
  Cell* cell = Cell_new(Cell_first(self), NULL);
  assert(cell != NULL);
  if(N == 1) return cell;
  Func* func = Lambda_Take_new(N-1, self);  // copy of self made later
  assert(func != NULL);
  cell->cdr = func;
  return cell;
}

/******************************************************************************/
/*                                  Testing                                   */
/******************************************************************************/

int Cell_cons_test(){

  Cell* x = Cell_cons(5,NULL);
  Cell* y = Cell_cons(4, x);  
  Cell* z = Cell_cons(4, Cell_cons(5,NULL));
  Cell* t = Cell_cons(3,y);
  Cell* u = Cell_cons(2,t);
  Cell* v = Cell_cons(1,u);
  Cell* w = Cell_cons(0,v);

  printf("w.first = %d\n", Cell_first(w));                                  // 0
  printf("w.rest.first = %d\n", Cell_first(Cell_rest(w)));                  // 1
  printf("w.rest.rest.first = %d\n", Cell_first(Cell_rest(Cell_rest(w))));  // 2
  printf("w.rest.rest.rest.first = %d\n", 
      Cell_first(Cell_rest(Cell_rest(Cell_rest(w)))));                      // 3
  printf("w.rest.rest.rest.rest.first = %d\n", 
      Cell_first(Cell_rest(Cell_rest(Cell_rest(Cell_rest(w))))));           // 4
  printf("w.rest.rest.rest.rest.rest.first = %d\n", 
      Cell_first(Cell_rest(Cell_rest(Cell_rest(Cell_rest(Cell_rest(w)))))));// 5
  printf("w.rest.rest.rest.rest.rest.rest = %d\n", 
      Cell_rest(Cell_rest(Cell_rest(Cell_rest(Cell_rest(Cell_rest(w))))))); // Null

  Cell_delete(z);
  Cell_delete(w);
  return 0;
}

int basic_transition(int);
int Cell_fromTransition_test(){
  Cell* from2 = Cell_fromTransition(2,basic_transition);
  printf("from2.first = %d\n", Cell_first(from2));
  printf("from2.rest.first = %d\n", Cell_first(Cell_rest(from2)));
  printf("from2.rest.rest.first = %d\n", Cell_first(Cell_rest(Cell_rest(from2))));
  Cell_delete(from2);
}

/******************************************************************************/
/*                                   Main                                     */
/******************************************************************************/

int basic_transition(int n){ return n + 1; }

int main(int argc, char* argv[]){
  assert(argc == 2);  // a single argument expected
  int numPrimes = atoi(argv[1]);
  Cell* from2 = Cell_fromTransition(2,basic_transition);
  Cell* x = Cell_take(from2, 2);



  Cell_delete(x);
  long checkSum = memory_log(NULL,NULL);
  if(checkSum != 0){
    fprintf(stderr, "Memory leak was detected\n");
    return -1;
  }

  return 0;
}
