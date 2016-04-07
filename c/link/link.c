// link.c
#include "link.h"
#include "link_node.h"
#include <malloc.h>
#include <assert.h>

long Link_log(const char* message, const void* address){
  static long memory_checksum = 0L;
  if((message == NULL) && (address == NULL)) return memory_checksum;
  assert(message != NULL);
  assert(address != NULL);
  fprintf(stderr, message, address);  // include '%lx' in 'message'
  memory_checksum ^= (long) address;
  return 0L;
}

int Link_hasMemoryLeak(){
  return (Link_log(NULL,NULL) != 0L) ? 1 : 0;
}

struct Link_ {
  int       refcount;
  LinkNode* head;
};

Link* Link_new(){
  Link* ptr = (Link*) malloc(sizeof(Link));
  assert(ptr != NULL);
  Link_log("Allocating new Link-ed list %lx\n", ptr);
  ptr->refcount = 1;
  ptr->head     = NULL;
  return ptr;
}

Link* Link_copy(Link* self){
  assert(self != NULL);
  self->refcount++;
  Link_log("Making copy of Link-ed list %lx\n", self);
  return self;
}

void Link_delete(Link* self){
  assert(self != NULL);
  assert(self->refcount > 0);
  self->refcount--;
  if(self->refcount == 0){
    if(self->head != NULL) LinkNode_delete(self->head);
    self->head = NULL;
    Link_log("Deallocating Link-ed list %lx\n", self);
    free(self);
  } else {
    Link_log("Deleting copy of Link-ed list %lx\n", self);
  }
}


int Link_isEmpty(Link* self){
  assert(self != NULL);
  return (self->head == NULL) ? 1 : 0;
}

// function takes ownership of node argument              // (0)
static LinkNode *insert_node(LinkNode* node, int key, void* value){
  if(node == NULL) return LinkNode_new(key, value);
  if(key == LinkNode_key(node)){    // duplicate key
    LinkNode_setValue(node, value); // updating value of existing key
    return node;                    // returning original node
  } else {
    // As we have no garbage collector, the most difficult part 
    // of understanding the code is figuring out its 'memory semantics'
    // namely working out who is responsible for deallocating various
    // objects. Is it the callee (i.e. function body) of the caller?
    // 
    LinkNode* next = LinkNode_copy(LinkNode_next(node));  // (1)
    LinkNode* new_next = insert_node(next, key, value);   // (2)
    LinkNode_setNext(node, new_next);                     // (3)
    return node;                                          // (4)
  }
}




