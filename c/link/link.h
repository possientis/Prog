// link.h
#ifndef INCLUDE_LINK_H
#define INCLUDE_LINK_H
#include <sys/types.h>  // size_t

typedef struct Link_      Link;
typedef struct LinkIter_  LinkIter;

Link*     Link_new();
Link*     Link_copy(Link* self);
void      Link_delete(Link* self);

void      Link_insert(Link* self, int key, void* value);
void      Link_remove(Link* self, int key);
int       Link_find(Link* self, int key, void** result);  // found -> 1, else 0
int       Link_isEmpty(Link* self);
LinkIter* Link_iter(Link* self);              // returns iterator object
void      Link_toString(Link* self, char* buf, size_t size);
int       Link_hasMemoryLeak(); 


#endif
