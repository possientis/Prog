// Decorator Design Pattern

#include <stdio.h>
#include <assert.h>
#include <malloc.h>

typedef struct VirtualTable_ VirtualTable;

long memory_log(const char* message, const void* ptr){
  static long memory_check = 0L;
  if(message == NULL && ptr == NULL) return memory_check;
  assert(message != NULL);
  assert(ptr != NULL);
  fprintf(stderr, message, ptr);
  memory_check ^= (long) ptr;
  return 0L;
}

/******************************************************************************/
/*                               VirtualTable                                 */
/******************************************************************************/

struct VirtualTable_ {
  int count;    // reference count
  const char*   (*description)(void* self);
  double        (*cost)(void* self);
  void          (*delete)(void* self);
};

VirtualTable* VirtualTable_copy(VirtualTable* self){
  assert(self != NULL);
  memory_log("Making copy of virtual table %lx\n", self);
  self->count++;
  return self;
}

VirtualTable* VirtualTable_new(
    const char* (*description)(void*),
    double      (*cost)(void*),
    void        (*delete)(void*)){

  assert(description != NULL);
  assert(cost != NULL);
  assert(delete != NULL);
  VirtualTable* ptr = (VirtualTable*) malloc(sizeof(VirtualTable));
  memory_log("Allocating new virtual table %lx\n", ptr);
  assert(ptr != NULL);
  ptr->count        = 1; // first reference
  ptr->description  = description;
  ptr->cost         = cost;
  ptr->delete       = delete;
  return ptr;
}
  
void VirtualTable_delete(VirtualTable* self){
  assert(self != NULL);
  assert(self->count > 0);
  self->count--;
  if(self->count == 0){ // deallocation needed
    self->description = NULL;
    self->cost        = NULL;
    self->delete      = NULL;
    memory_log("Deallocating existing virtual table %lx\n", self);
    free(self);
  }
  else                { // just logging
    memory_log("Deleting copy of virtual table %lx\n", self);
  }
}

/******************************************************************************/
/*                            Pizza virtual table                             */
/******************************************************************************/
const char* _Pizza_description(void* self){
  // TBI
}

double _Pizza_cost(void* self){
  // TBI
}

void _Pizza_delete(void* self){
  // TBI
}

VirtualTable* Pizza_VirtualTable_new(){
  return VirtualTable_new(_Pizza_description, _Pizza_cost, _Pizza_delete);
}

VirtualTable* Pizza_VirtualTable_Instance(int release){
  static VirtualTable* instance = NULL;
  assert(release == 0 || release == 1);
  if(release == 1){               // virtual table instance is deallocated
    assert(instance != NULL);
    assert(instance->count == 1); // last reference
    VirtualTable_delete(instance);
    instance = NULL;
    return NULL;
  }
  else { // TBI
  }
}





int main(){

  assert(memory_log(NULL,NULL) == 0L);  // no memory leak detected
  return 0;
}

