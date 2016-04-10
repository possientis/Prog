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
  //fprintf(stderr, message, address);  // include '%lx' in 'message'
  memory_checksum ^= (long) address;
  return 0L;
}

int Link_hasMemoryLeak(){
  return (Link_log(NULL,NULL) != 0L) ? 1 : 0;
}

/******************************************************************************/
/*                                Link Class                                  */
/******************************************************************************/

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



// function has ownership of argument, caller has ownership of returned object-(0)
static LinkNode *insert_node(LinkNode* node, int key, const void* value){
  if(node == NULL) return LinkNode_new(key, value);
  if(key == LinkNode_key(node)){    // duplicate key
    LinkNode_setValue(node, value); // updating value of existing key
    return node;                    // returning original node
  } else {
    // As we have no garbage collector, the most difficult part 
    // of understanding the code is figuring out its 'memory semantics'
    // namely working out who is responsible for deallocating various
    // objects. Is it the callee (i.e. function body) of the caller?
    // (0) : function takes ownership of node, which we need to deallocate
    // (1) : LinkNode_next does not give ownership of returned object
    // However, we are making a copy, so we also need to deallocate next 
    // (2) : insert_node takes ownership of argument. So we lose the 
    // duty to deallocate next. However, we need to deallocate new_next
    // (3) : LinkNode_setNext takes ownership of new_next, so we lose 
    // duty to deallocate it. 
    // (4) : at this point, function body is only responsible for 
    // deallocating node. However, we are returning node, passing on
    // responsibility to function caller. So no more action required.
    LinkNode* next = LinkNode_next(node);                 // (1)
    if(next != NULL) next = LinkNode_copy(next);
    LinkNode* new_next = insert_node(next, key, value);   // (2)
    LinkNode_setNext(node, new_next);                     // (3)
    return node;                                          // (4)
  }
}

// function has ownership of argument, caller has ownership of returned object
static LinkNode* delete_node(LinkNode* node, int key){
  if(node == NULL) return NULL;   // no impact on empty list
  if(key == LinkNode_key(node)){  // key found, return next
    LinkNode* next = LinkNode_next(node);
    if(next != NULL) next = LinkNode_copy(next);
    LinkNode_delete(node);  // function is responsible for deallocating node
    return next;            // passing on owenership to caller
  } else {
    LinkNode* next = LinkNode_next(node);
    if(next != NULL) next = LinkNode_copy(next);
    LinkNode* new_next = delete_node(next, key);
    LinkNode_setNext(node, new_next);
    return node;
  }
}

// return 1 if key found, 0 otherwise. Caller keeps owenership of argument
static int search_node(LinkNode* node, int key, const void** result){ 
  assert(result != NULL);
  if(node == NULL) {    // search failure
    *result = NULL;     // no real need, just to make error catching easier
    return 0;
  }
  if(key == LinkNode_key(node)){
    *result = LinkNode_value(node);
    return 1;
  } else {
    return search_node(LinkNode_next(node), key, result);
  }
}
    
int Link_isEmpty(Link* self){
  assert(self != NULL);
  return (self->head == NULL) ? 1 : 0;
}

void Link_insert(Link* self, int key, const void* value){
  assert(self != NULL);
  self->head = insert_node(self->head, key, value);
}

void Link_remove(Link* self, int key){
  assert(self != NULL);
  self->head = delete_node(self->head, key);
}

int Link_find(Link* self, int key, const void** result){
  assert(self != NULL);
  return search_node(self->head, key, result);
}

/******************************************************************************/
/*                              LinkIter Class                                */
/******************************************************************************/

struct LinkIter_ {
  int refcount;
  LinkNode* current;
  LinkNode* next; 
};

// does not take ownership of list argument
LinkIter* LinkIter_new(Link* list){
  assert(list != NULL);
  LinkIter* ptr = (LinkIter*) malloc(sizeof(LinkIter));
  assert(ptr != NULL);
  Link_log("Allocating new Link iterator %lx\n", ptr);
  ptr->refcount = 1;
  ptr->current  = NULL;
  ptr->next     = list->head;
}

LinkIter* LinkIter_copy(LinkIter* self){
  assert(self != NULL);
  self->refcount++;
  Link_log("Making copy of Link iterator %lx\n", self);
  return self;
}

void LinkIter_delete(LinkIter* self){
  assert(self != NULL);
  assert(self->refcount > 0);
  self->refcount--;
  if(self->refcount == 0){
    self->current = NULL; // iterator does not have ownership, no deallocation
    self->next    = NULL; // iterator does not have ownership, no deallocation
    Link_log("Deallocating Link iterator %lx\n", self);
    free(self);
  } else {
    Link_log("Deleting copy of Link iterator %lx\n", self);
  }
}


int LinkIter_hasNext(LinkIter* self){
  assert(self != NULL);
  return (self->next != NULL) ? 1 : 0;
}

void LinkIter_moveNext(LinkIter* self){
  assert(self != NULL);
  assert(self->next != NULL);
  self->current = self->next;
  self->next = LinkNode_next(self->current);
}

int LinkIter_key(LinkIter* self){
  assert(self != NULL);
  assert(self->current != NULL);
  return LinkNode_key(self->current);
}


const void* LinkIter_value(LinkIter* self){
  assert(self != NULL);
  assert(self->current != NULL);
  return LinkNode_value(self->current);
}
  








