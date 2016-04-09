// link_node.c
#include "link_node.h"
#include <malloc.h>
#include <assert.h>

long LinkNode_log(const char* message, const void* address){
  static long memory_checksum = 0L;
  if((message == NULL) && (address == NULL)) return memory_checksum;
  assert(message != NULL);
  assert(address != NULL);
  //fprintf(stderr, message, address);  // include '%lx' in 'message'
  memory_checksum ^= (long) address;
  return 0L;
}

int LinkNode_hasMemoryLeak(){
  return (LinkNode_log(NULL,NULL) != 0L) ? 1 : 0;
}

struct LinkNode_ {
  int         refcount;
  int         key;
  const void* value;
  LinkNode*   next;
};

LinkNode* LinkNode_new(int key, const void* value){
  LinkNode* ptr = (LinkNode*) malloc(sizeof(LinkNode));
  assert(ptr != NULL);
  LinkNode_log("Allocating new LinkNode %lx\n", ptr);
  ptr->refcount = 1;
  ptr->key      = key;
  ptr->value    = value;
  ptr->next     = NULL; 
}

LinkNode* LinkNode_copy(LinkNode* self){
  assert(self != NULL);
  LinkNode_log("Making copy of LinkNode %lx\n", self);
  self->refcount++;
  return self;
}

void LinkNode_delete(LinkNode* self){
  assert(self != NULL);
  assert(self->refcount > 0);
  self->refcount--;
  if(self->refcount == 0){
    self->key   = 0;
    self->value = NULL;
    if(self->next != NULL) LinkNode_delete(self->next);
    self->next  = NULL;
    LinkNode_log("Deallocating LinkNode %lx\n", self);
    free(self);
  } else {
    LinkNode_log("Deleting copy of LinkNode %lx\n", self);
  }
}

int LinkNode_key(LinkNode* self){
  assert(self != NULL);
  return self->key;
}

const void* LinkNode_value(LinkNode* self){
  assert(self != NULL);
  return self->value;
}

LinkNode* LinkNode_next(LinkNode* self){
  assert(self != NULL);
  return self->next;
}

void LinkNode_setNext(LinkNode* self, LinkNode* next){
  assert(self != NULL);
  if(self->next !=NULL) LinkNode_delete(self->next);
  self->next = next;
}

void LinkNode_setValue(LinkNode* self, const void* value){
  assert(self != NULL);
  self->value = value;
}







    








