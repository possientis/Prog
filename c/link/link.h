// link.h
#ifndef INCLUDE_LINK_H
#define INCLUDE_LINK_H
#include <sys/types.h>  // size_t

typedef struct Link_      Link;
typedef struct LinkIter_  LinkIter;

// interface for Link-ed list
Link*       Link_new();
Link*       Link_copy(Link* self);
void        Link_delete(Link* self);
void        Link_insert(Link* self, int key, const void* value);
void        Link_remove(Link* self, int key);
int         Link_find(Link* self, int key, const void** result); // found -> 1
int         Link_isEmpty(Link* self);
void        Link_toString(Link* self, char* buf, size_t size);
int         Link_hasMemoryLeak(); 

// interface for Link-ed list iterator
LinkIter*   LinkIter_new(Link* list);
LinkIter*   LinkIter_copy(LinkIter* self);
void        LinkIter_delete(LinkIter* self);
int         LinkIter_hasNext(LinkIter* self);
void        LinkIter_moveNext(LinkIter* self);
int         LinkIter_key(LinkIter* self);
const void* LinkIter_value(LinkIter* self);

#endif
