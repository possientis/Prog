// dict.c
#include "dict.h"
#include <malloc.h>
#include <assert.h>

// basic safety scheme against memory leaks
long Dictionary_log(const char* message, const void* address){
  static long memory_check = 0L;
  // Dictionary_log(NULL,NULL) returns current memory_check
  if((message == NULL) && (address == NULL)) return memory_check;
  assert(message != NULL);
  assert(address != NULL);
  // message should contain %lx so fprintf expects third 'address' argument
  fprintf(stderr, message, address);  // uncomment this line when needed
  memory_check ^= (long) address;     // xor-ing address as sanity check
  return 0L;
}

int Dictionary_hasMemoryLeak(){
  return (Dictionary_log(NULL, NULL) != 0L ? 1 : 0);
}

struct Dictionary_ {
  int           refcount;     // reference count to Dictionary object
  int           num;          // number of entries
  int           size;         // allocated space
  int           isMemEnabled; // flag enabling memory allocation or deallocation
  void**        data;
};


Dictionary* Dictionary_new(){
  Dictionary* ptr = (Dictionary*) malloc(sizeof(Dictionary));
  assert(ptr != NULL);
  Dictionary_log("Allocating new dictionary %lx\n", ptr);
  void** data = (void**) malloc(4*sizeof(void*));
  assert(data != NULL);
  Dictionary_log("Allocating data array %lx\n", data);

  ptr->refcount     = 1;    // returned pointer is unique existing reference
  ptr->num          = 0;    // created dictionary is empty
  ptr->size         = 4;    // dictionary can hold items initially
  ptr->isMemEnabled = 1;    // allows further memory allocation or deallocation
  ptr->data         = data;
}

Dictionary* Dictionary_copy(Dictionary* self){
  assert(self != NULL);
  Dictionary_log("Making copy of dictionary %lx\n", self);
  self->refcount++;
  return self;
}

// The dictionary does not have ownership of objects pointed to by pointers
// it stores. Hence deallocation of data array simply consists in freeing pointer.
void Dictionary_delete(Dictionary* self){
  assert(self != NULL);
  self->refcount--;
  if(self->refcount == 0){
    assert(self->data != NULL);
    Dictionary_log("Deallocating data array %lx\n", self->data);
    free(self->data);
    self->num           = 0;
    self->size          = 0;
    self->isMemEnabled  = 0;
    self->data          = NULL;
    Dictionary_log("Deallocating dictionary %lx\n", self);
    free(self);
  } else {
    Dictionary_log("Deleting copy of dictionary %lx\n", self);
  }
}
    




