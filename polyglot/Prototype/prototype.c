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
  int alive;                  // 1 (alive) or 0 (dead)
  int refcount;               // counting instances of base class Cloneable
  Cloneable* (*clone)(Cloneable* self);
  void (*delete)(Cloneable* ptr);
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
  ptr->refcount = 0;
  ptr->alive = 1;
}

// destroy
void Cloneable_ops_destroy(struct Cloneable_ops* ptr){
  assert(ptr != NULL);
  ptr->clone = NULL;
  ptr->refcount = 0;
  ptr->alive = 0;
}

// new
struct Cloneable_ops* Cloneable_ops_new(Cloneable* (*func)(Cloneable*)){
  struct Cloneable_ops* ptr = (struct Cloneable_ops*) malloc(
      sizeof(struct Cloneable_ops)
  );
  assert(ptr != NULL);
  Cloneable_ops_init(ptr, func);
  assert(ptr->refcount == 0);
  assert(ptr->alive == 1);
  assert(ptr->clone == func);
  return ptr;
}

// delete
void Cloneable_ops_delete(struct Cloneable_ops* ptr){
  assert(ptr != NULL);
  Cloneable_ops_destroy(ptr);
  free(ptr);
}


struct Cloneable_ops* Cloneable_ops_Cloneable_get_instance(){
  static struct Cloneable_ops* instance = NULL;

  if(instance != NULL && instance->alive == 0){
    instance = NULL;  //instance was stale
  }
  if(instance == NULL){
    instance = Cloneable_ops_new(Cloneable_ops_clone);
    assert(instance != NULL);
    assert(instance->refcount == 0);
    assert(instance->alive == 1);
    assert(instance->clone == Cloneable_ops_clone);
  }

  assert(instance != NULL);
  assert(instance->refcount >= 0);
  assert(instance->alive == 1);
  assert(instance->clone == Cloneable_ops_clone);
  instance->refcount++;
  return instance;
}

void Cloneable_ops_Cloneable_free_instance(struct Cloneable_ops* ptr){
  assert(ptr != NULL);
  assert(ptr->refcount > 0);
  assert(ptr->alive = 1);
  assert(ptr->clone = Cloneable_ops_clone);
  ptr->refcount--; 
  if(ptr->refcount == 0){
    Cloneable_ops_destroy(ptr);
    free(ptr);
  }
}

typedef struct Cloneable_ Cloneable;  // see below
struct Cloneable_ {
  void *obj;                  // concrete object
  struct Cloneable_ops* ops;  // concrete implementation of virtual clone
};

void Cloneable_init(Cloneable* ptr, void* obj, struct Cloneable_ops* ops){
  assert(ptr != NULL);
  ptr->obj = obj;
  ptr->ops = ops;
}

void Cloneable_destroy(Cloneable* ptr){
  assert(ptr != NULL);
  ptr->obj = NULL;
  ptr->ops = NULL;
}

Cloneable* Cloneable_new(){
  Cloneable* ptr = (Cloneable*) malloc(sizeof(Cloneable));
  assert(ptr != NULL);
  void* obj = (void*) ptr;
  struct Cloneable_ops* ops = Cloneable_ops_Cloneable_get_instance();
  Cloneable_init(ptr,obj,ops);
  return ptr;
}

void Cloneable_delete(Cloneable* ptr){
  assert(ptr != NULL);

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
  //
  ptr = Cloneable_ops_Cloneable_get_instance();
  assert(ptr != NULL);
  assert(ptr->refcount == 1);
  ptr = Cloneable_ops_Cloneable_get_instance();
  assert(ptr->refcount == 2);
  ptr->clone(NULL);
  Cloneable_ops_Cloneable_free_instance(ptr);
  assert(ptr->refcount == 1);
  Cloneable_ops_Cloneable_free_instance(ptr);
  ptr = Cloneable_ops_Cloneable_get_instance();
  assert(ptr->refcount == 1);
  ptr = Cloneable_ops_Cloneable_get_instance();
  assert(ptr->refcount == 2);
  Cloneable_ops_Cloneable_free_instance(ptr);
  Cloneable_ops_Cloneable_free_instance(ptr);
}


int main(int argc, char* argv[]){

  basic_test();
  return 0;
}


