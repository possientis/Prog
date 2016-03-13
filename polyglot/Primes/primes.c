#include <stdio.h>
#include <malloc.h>
#include <assert.h>
#include <stdlib.h> // atoi
#include <string.h> // strcpy, strcat


typedef struct Cell_    Cell;
typedef struct Func_    Func;
typedef struct String_  String;

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
/*                               String class                                 */
/******************************************************************************/

// attempt at creating a class of immutable strings. C++ is not allowed here
// cut and pasting from previous C exercise (composite), not too proud about it

struct String_ {
  int count;      // reference count
  int length;
  const char* buffer;
};

String* String_new(const char* from){
  assert(from != NULL);
  int length = strlen(from); // risky, buffer could have no trailing '\0'
  assert(length >= 0);
  char* buffer = (char*) malloc(sizeof(char)*(length + 1));
  memory_log("allocating string buffer %lx\n", buffer);
  assert(buffer != NULL);
  String* obj = (String*) malloc(sizeof(String));
  memory_log("allocating string object %lx\n", obj);
  assert(obj != NULL);
  obj->count = 1;
  obj->length = length;
  obj->buffer = buffer;
  strcpy(buffer,from);
  return obj;
}

String* String_copy(String* self){
  assert(self != NULL);
  assert(self->count > 0);
  assert(self->buffer != NULL);
  memory_log("making copy of string object %lx\n", self);
  self->count++;  // increasing reference count
  return self;
}

void String_delete(String* self){
  assert(self != NULL);
  assert(self->count > 0);
  assert(self->buffer != NULL);
  self->count--;                 // decresing reference count
  if(self->count == 0){
    memory_log("deallocating string buffer %lx\n", (void*) self->buffer);
    free((char*)self->buffer);  // casting const away for memory release
    self->buffer = NULL;
    self->length = 0;
    memory_log("deallocating string object %lx\n", self);
    free(self);
  }
  else{
    memory_log("deleting copy of string object %lx\n",self);
  }
}

// takes ownership of both strings, which do not need deallocation by caller
String *String_append(String* str1, String* str2){
  assert(str1 != NULL);
  assert(str2 != NULL);
  int len1 = str1->length;
  int len2 = str2->length;
  int len = len1 + len2;
  char* buffer = (char*) malloc(sizeof(char) * (len + 1));
  assert(buffer != NULL);
  memory_log("allocating string buffer %lx for append operation\n", buffer);
  strcpy(buffer, str1->buffer);
  strcat(buffer, str2->buffer);
  String* obj = (String*) malloc(sizeof(String)); 
  memory_log("allocating string object %lx for append operation\n", obj);
  assert(obj != NULL);
  obj->count = 1;
  obj->length = len;
  obj->buffer = buffer;
  String_delete(str1);
  String_delete(str2);
  return obj; 
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


// In a normal function call Func* f(Func* x), you would expect by convention
// that the caller would lose ownership of object x (i.e. would no longer need to 
// deallocate object) and gain ownership for returned object. The copy function
// creates an exception to this rule: the caller has ownership of returned 
// object as expected (i.e is responsible for its deallocation), but it also
// remains reponsible for the deallocation of x, i.e. it retains ownership of x


// generic boiler-plate code for copy
Func* Func_copy(Func* self){
  assert(self != NULL);
  memory_log("Making copy of functional %lx\n", self);
  self->count++;
  return self;
}


// generic boiler-plate code for heap allocation
// usual convention apply: caller has sole ownership of returned Func object
// but loses ownership (duty to deallocate) of passed data object
Func* Func_new(
    void* data,                           // caller, loses ownership of data
    void* (*code)(void*,void*),           // static data, no issue of ownership
    void  (*delete)(Func* self)           // static data, no issue of ownership
){
  Func* ptr = (Func*) malloc(sizeof(Func));
  assert(ptr != NULL);
  memory_log("Allocating new functional %lx\n", ptr);
  ptr->count = 1;   // single ownership attributed to caller
  ptr->data = data; // hopefully, virtual destructor will reflect ownership
  ptr->code = code;
  ptr->delete = delete;
  return ptr;       // caller has sole ownership of object (no copy)
}

// generic boiler-plate code for destruction, virtual deallocation
// The caller loses ownership of self (no longer need to deallocate)
void* Func_delete(Func* self){
  assert(self != NULL);
  assert(self->count > 0);
  self->count--;                // decreasing reference count;
  if(self->count == 0){         // memory deallocation needs to take place
    void(*delete)(Func*);     
    delete = self->delete;      // retrieving object's virtual destructor
    delete(self);               // calling virtual destructor on object
  }
  else{                         // reference count was decreased. Done.
    memory_log("Deleting copy of functional %lx\n", self);
  }
}

// Func object encapsulates data and code, and gives us a 'call' method
// Here is a case were we are simply calling a method on object self
// the caller does not wish to lose ownership of object, and should
// remain responsible for its deallocation. So this function does not
// implement the usual convention of taking ownership of argument pointer.
void* Func_call(Func* self, void* args){
  assert(self != NULL);
  // since this function does not take ownership of object, and object
  // has ownership of its data, in order to ensure this semantics is
  // respected, we need to ensure that any 'code' member of Func object
  // does not take ownership of its first argument.
  return self->code(self->data, args);
}

/******************************************************************************/
/*                               () -> value                                  */
/******************************************************************************/

// Given a value of type Cell*, we need to instantiate a Func object which
// represents the lambda expression () -> value. This is the simplest case.
// The Func object requires three elements, data, code and destructor.

Cell* Cell_copy(Cell* self);  // forward

void* Lambda_Wrapper_code(void* data, void* args){
  // As indicated with the Func_call function above, Lambda_Wrapper_code,
  // should not take ownership of its data pointer argument, whose deallocation
  // responsibility remains with the caller. However, a Cell* pointer is returned
  // and caller expects to be responsible for that. It follows that we should 
  // return a copy, so that caller has deallocation responsibility both for
  // data and returned object.
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

// Usual convention apply: caller has sole ownership of returned Func object
// but loses ownership (duty to deallocate) of passed object value. 
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
// exception ot usual convention: caller does have sole ownership to returned
// object (duty to deallocate) but retains obligation to deallocate passed in
// object, i.e. retains ownership of self.
Cell* Cell_copy(Cell* self){
  assert(self != NULL);
  memory_log("Making copy of cell %lx\n", self);
  self->count++;
  return self;
}


// generic boiler-plate code for heap allocation
// usual convetion apply: caller has sole ownership of returned Cell object,
// but loses ownership (duty to deallocate) of passed in Func object.
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
      Cell_delete(self->cache); // Cell has ownership of its data
      self->cache = NULL;
    }
    if(self->cdr != NULL){
      Func_delete(self->cdr);   // Cell has ownership of its Func
      self->cdr   = NULL;
    }
    memory_log("Deallocating existing cell %lx\n", self);
    free(self);
  }
  else{                         // reference count was decreased. Done.
    memory_log("Deleting copy of cell %lx\n", self);
  }
}

// method call: usual convention does not apply for self, as caller retains
// ownership of self (duty to deallocate).
int Cell_first(Cell* self){
  assert(self != NULL);
  return self->car;
}

// This is also a method call: in order to keep up with established pattern,
// caller should be responsible to deallocate returned object, while keeping
// responsibility to deallocate self. Since self is responsible for its 
// encapsulated data this means that a copy should be returned.

Cell* Cell_rest(Cell* self){
  assert(self != NULL);
  if(self->cache != NULL){ 
    return Cell_copy(self->cache);  // both caller and self are responsible now
  }
  if(self->cdr == NULL){            // thunk is null
    return NULL;
  }
  // As indicated above when defining Func_call, the function should leave
  // self with its obligation to deallocate self->cdr. However, full the 
  // returned Cell object also become self's responsibility.
  self->cache = (Cell*) Func_call(self->cdr,NULL);

  // Assuming self->cdr has no side effect, having evaluated its value with 
  // NULL as arguments, we no longer need to keep the object alive.
  // self has owenership of Func object and can proceed to deallocate
  Func_delete(self->cdr);       
  self->cdr = NULL;     

  return Cell_copy(self->cache);      // both caller and self are responsible now 
} 

// usual convention applies: caller loses ownership of rest (duty to deallocate)
// but gains ownerhips of returned object.
Cell* Cell_cons(int first, Cell* rest){
  Func* func;
  if(rest != NULL){
    func = Lambda_Wrapper_new(rest);  // duty to deallocate rest is lost
  }
  else{
    func = NULL;
  }
  // we solely own the func object at this stage
  return Cell_new(first, func);       // ownership of func passed on to caller
} 

// This is a method call. Caller retains ownership of self (duty to deallocate)
// and gains full ownership of returned string object
String* Cell_toString(Cell* self){
  char buffer[24];        // stack allocated buffer to hold representation of int
  assert(self != NULL);
  String* str = String_new("(");
  String* space = String_new(" ");
  Cell* next = Cell_copy(self);   // we need to deallocate as we take copy
  int start = 1;          // boolean flag to decide on separating with " "
  while(next != NULL){
    if(start == 0){
      str = String_append(str, String_copy(space));
    }
    else{
      start = 0;
    }
  sprintf(buffer, "%d", Cell_first(next));
  String* temp = String_new(buffer);
  str = String_append(str,temp);
  Cell* old = next;               // we need to deallocate
  next = Cell_rest(next);         // we need to dealloc next
  Cell_delete(old);
  }

  str = String_append(str, String_new(")"));
  String_delete(space);
  return str;
}


/******************************************************************************/
/*                      () -> fromTransition(init,transition)                 */
/******************************************************************************/

// Given a transition function transition:int->int, and a initial value x:int
// we need be able to represent the lambda () -> fromTransition(x,transition)
// where fromTransition is defined below and returns a Cell*. The data which 
// is encapsulated is thus an integer together with the transition function:

typedef struct TransData_ TransData;
struct TransData_ {
  int init;
  int (*transition)(int);
};


// The Func object representing lambda expression requires data
// The function pointer argument being statically allocated, we
// do not need to discuss ownership. However, this function 
// returns an object whose owenership falls on the caller.
void* Lambda_Transition_data(int init, int (*transition)(int)){
  assert(transition != NULL);
  TransData* data = (TransData* ) malloc(sizeof(TransData));
  assert(data != NULL);
  memory_log("Allocating transition data %lx\n", data);
  data->init = init;
  data->transition = transition;
  return (void*) data;
}


Cell* Cell_fromTransition(int init, int (*transition)(int));  // forward

// The Func object representing lambda expression requires code

void* Lambda_Transition_code(void* data, void* args){
  // As indicated with the Func_call function above, Lambda_Transition_code
  // should not take ownership of its data pointer argument, whose deallocation
  // responsibility remains with the caller. However, a Cell* pointer is returned
  // and caller expects to be responsible for that.
  assert(data != NULL);
  TransData* trans = (TransData*) data;
  int init = trans->init;
  int (*transition)(int);
  transition = trans->transition;
  // Cell_fromTransition gives us ownership of returned object which is 
  // passed on immediately to caller of this function
  return Cell_fromTransition(init, transition);
}

// The Func object representing lambda expression requires destructor
void Lambda_Transition_delete(Func* self){
  assert(self != NULL);
  assert(self->count == 0);
  TransData* trans = (TransData*) self->data;  
  memory_log("Deallocating transition data %lx\n", trans);
  free(trans);              // Func is responsible for its encapsulated data
  self->data    = NULL;
  self->code    = NULL;
  self->delete  = NULL;
  memory_log("Deallocating functional %lx\n", self);
  free(self);
}

// caller has sole ownership of returned Func object
Func* Lambda_Transition_new(int init, int (*transition)(int)){
  return Func_new(
      Lambda_Transition_data(init, transition), // Func has ownership
      Lambda_Transition_code,
      Lambda_Transition_delete
  );
}

// caller has sole ownership of returned Cell object
Cell* Cell_fromTransition(int init, int (*transition)(int)){
  assert(transition != NULL);
  Func* func = Lambda_Transition_new(transition(init), transition);
  assert(func != NULL);
  return Cell_new(init,func); // new cell has ownership of Func
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
// The usual convention should apply. Caller should lose ownership
// of the passed in Cell object, but gain full ownership of the 
// returned object.
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
  // As indicated with the Func_call function above, Lambda_Take_code
  // should not take ownership of its data pointer argument, whose 
  // deallocation responsibility remains with the caller. However, 
  // a Cell* pointer is returned and caller expects to be responsible for that.

  assert(data != NULL);
  TakeData* take = (TakeData*) data;
  int value = take->value;
  Cell* cell = take->cell;                  // cell is owned by data
  // Cell_rest does not affect ownership of of cell, and gives us 
  // full ownership of return object rest
  Cell* rest = Cell_rest(cell);
  // Cell_take is a method call: to be consistent, it should leave ownership
  // of self to the caller, but provide full ownership of the returned object
  Cell* out = Cell_take(rest, value);
  // we are still responsible for rest which should be deallocated
  Cell_delete(rest);
  // ownership of out is passed duly passed on to caller
  return out;
}

// The Func object representing lambda expression requires destructor
void Lambda_Take_delete(Func* self){
  assert(self != NULL);
  assert(self->count == 0);
  TakeData* take = (TakeData*) self->data;  
  assert(take != NULL);
  Cell* cell = take->cell;  // take has ownership
  Cell_delete(cell);
  memory_log("Deallocating take data %lx\n", take);
  free(take);   // Func object is responsible for its internal data
  self->data    = NULL;
  self->code    = NULL;
  self->delete  = NULL;
  memory_log("Deallocating functional %lx\n", self);
  free(self);
}

// usual convention applies: caller loses ownership of passed in object, but
// gains full ownership of returned object
Func* Lambda_Take_new(int value, Cell* cell){
  return Func_new(
      Lambda_Take_data(value, cell),
      Lambda_Take_code,
      Lambda_Take_delete
  );
}


// Cell_take is a method call: to be consistent, it should leave ownership
// of self to the caller, but provide full ownership of the returned object
Cell* Cell_take(Cell* self, int N){
  assert(self != NULL);
  assert(N > 0);
  Cell* cell = Cell_new(Cell_first(self), NULL);
  assert(cell != NULL);
  if(N == 1) return cell;
  Func* func = Lambda_Take_new(N-1, Cell_copy(self));  
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

  // to enable easier reasoning on memory allocation and object ownership 
  // (duty to deallocate), we made certain choices on the semantics of 
  // functions which return objects or use them as arguments.
  // In particular we decided that Cell* Cell_rest(Cell* self) should
  // provide full ownership of returned object, but without taking over
  // ownership of passed in object. This means that we lose the syntactic
  // convenience of chained calls Cell_rest(Cell_rest(self)) as this would
  // lead to memory leaks.
  
  Cell* w0 = w;
  Cell* w1 = Cell_rest(w0);
  Cell* w2 = Cell_rest(w1);
  Cell* w3 = Cell_rest(w2);
  Cell* w4 = Cell_rest(w3);
  Cell* w5 = Cell_rest(w4);


  printf("w.first = %d\n", Cell_first(w0));                           // 0
  printf("w.rest.first = %d\n", Cell_first(w1));                      // 1
  printf("w.rest.rest.first = %d\n", Cell_first(w2));                 // 2
  printf("w.rest.rest.rest.first = %d\n", Cell_first(w3));            // 3
  printf("w.rest.rest.rest.rest.first = %d\n", Cell_first(w4));       // 4
  printf("w.rest.rest.rest.rest.rest.first = %d\n", Cell_first(w5));  // 5
  printf("w.rest.rest.rest.rest.rest.rest = %d\n", Cell_rest(w5));    // 0

  Cell_delete(z);
  Cell_delete(w0);
  Cell_delete(w1);
  Cell_delete(w2);
  Cell_delete(w3);
  Cell_delete(w4);
  Cell_delete(w5);

  return 0;
}

int basic_transition(int);
int Cell_fromTransition_test(){
  Cell* from2 = Cell_fromTransition(2,basic_transition);
  Cell* from3 = Cell_rest(from2);
  Cell* from4 = Cell_rest(from3);

  printf("from2.first = %d\n", Cell_first(from2));            // 2
  printf("from2.rest.first = %d\n", Cell_first(from3));       // 3
  printf("from2.rest.rest.first = %d\n", Cell_first(from4));  // 4

  Cell_delete(from4);
  Cell_delete(from3);
  Cell_delete(from2);
}

int Cell_take_test(){

  Cell* from2 = Cell_fromTransition(2, basic_transition);
  Cell* from2to6 = Cell_take(from2,5);
  Cell* from3to6 = Cell_rest(from2to6);
  Cell* from4to6 = Cell_rest(from3to6);
  Cell* from5to6 = Cell_rest(from4to6);
  Cell* from6to6 = Cell_rest(from5to6);

  printf("x0 = %d\n", Cell_first(from2to6));    // 2
  printf("x1 = %d\n", Cell_first(from3to6));    // 3
  printf("x2 = %d\n", Cell_first(from4to6));    // 4
  printf("x3 = %d\n", Cell_first(from5to6));    // 5
  printf("x4 = %d\n", Cell_first(from6to6));    // 6
  printf("x5 = %d\n", Cell_rest(from6to6));     // 0 (NULL)

  String* str = Cell_toString(from2to6);
  printf("from2to6 = %s\n", str->buffer);


  String_delete(str);
  Cell_delete(from6to6);
  Cell_delete(from5to6);
  Cell_delete(from4to6);
  Cell_delete(from3to6);
  Cell_delete(from2to6);
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
  Cell* x = Cell_take(from2,numPrimes);
  String* str = Cell_toString(x);
  printf("%s\n",str->buffer);

  String_delete(str);
  Cell_delete(x);
  Cell_delete(from2);
  long checkSum = memory_log(NULL,NULL);
  if(checkSum != 0){
    fprintf(stderr, "Memory leak was detected\n");
    return -1;
  }

  return 0;
}
