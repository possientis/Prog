// Prototype design pattern
// Imagine that in order to instantiate certain objects we need to carry out
// expensive database queries. In order to improve performance, it would 
// be beneficial to cache whatever object is created from the database
// and return a copy of the cached object whenever a subsequent request
// for object instantiation arises.
#include <memory.h>
#include <stdio.h>
#include <assert.h>
#include <malloc.h>

// operations on Cloneable
typedef struct Cloneable_ Cloneable;  // see below
struct Cloneable_ops {
  Cloneable* (*clone)(Cloneable* self);
};

// possible value of 'clone' field
Cloneable* Cloneable_ops_clone(Cloneable* self){
  fprintf(stderr, "Cloneable::clone is not implemented\n");
  return NULL;
}

// init
void Cloneable_ops_init(struct Cloneable_ops* ptr, Cloneable* (*func)(Cloneable*)){
  assert(ptr != NULL);
  ptr->clone = func;
}

// destroy
void Cloneable_ops_destroy(struct Cloneable_ops* ptr){
  assert(ptr != NULL);
  ptr->clone = NULL;
}

// new
struct Cloneable_ops* Cloneable_ops_new(Cloneable* (*func)(Cloneable*)){
  struct Cloneable_ops* ptr = (struct Cloneable_ops*) malloc(
      sizeof(struct Cloneable_ops)
  );
  Cloneable_ops_init(ptr, func);
  return ptr;
}

// delete
void Cloneable_ops_delete(struct Cloneable_ops* ptr){
  assert(ptr != NULL);
  Cloneable_ops_destroy(ptr);
  free(ptr);
}

// there should only be one Cloneable operation instance per class
// shared by all instances of Cloneable. This function maintains a 
// reference count of all Cloneable instances.
int Cloneable_ops_refcount_base(int add){
  static int count = 0;  // reference counter     
  count += add;
  return count;
}

// maintains a unique pointer. reset = 1 to allocate new
struct Cloneable_ops_pointer_base(int reset){
}



struct Cloneable_ops* Cloneable_ops_get_instance_base(){
  static struct Cloneable_ops* instance = NULL; // unique instance for base class
  int refcount = Cloneable_ops_refcount_base(1);// one more Cloneable
  if(instance == NULL){     // no instance currently held
    assert(refcount == 1);  // it had to be zero prior to increment
    instance = Cloneable_ops_new(Cloneable_ops_clone);
  }
  assert(refcount > 0);
  assert(instance != NULL);
  return instance;
}

void Cloneable_ops_instance_free_instance_base(){
  int refcount = Cloneable_ops_refcount_base(-1);
  assert(refcount >= 0);
}


void basic_test(){
  // struct Cloneable_ops from stack
  struct Cloneable_ops op;
  Cloneable_ops_init(&op,Cloneable_ops_clone);
  op.clone(NULL);
  Cloneable_ops_destroy(&op);
  // struct Cloneable_ops from heap
  struct Cloneable_ops* ptr = Cloneable_ops_new(Cloneable_ops_clone);
  assert(ptr != NULL);
  ptr->clone(NULL);
  Cloneable_ops_delete(ptr);
}


int main(int argc, char* argv[]){

  basic_test();

  return 0;
}


