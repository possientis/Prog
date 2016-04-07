// link_node.h
#ifndef INCLUDE_LINK_NODE_H
#define INCLUDE_LINK_NODE_H


typedef struct LinkNode_ LinkNode;

LinkNode* LinkNode_new(int key, void* value); // does not take ownership of void*
LinkNode* LinkNode_copy(LinkNode* self);      // increments reference count
void      LinkNode_delete(LinkNode* self);    // decrements reference count or free
int       LinkNode_key(LinkNode* self);
void*     LinkNode_value(LinkNode* self);
LinkNode* LinkNode_next(LinkNode* self);      // make copy if you want to own
void      LinkNode_setNext(LinkNode* self, LinkNode* next); // takes ownership
void      LinkNode_setValue(LinkNode* self, void* value);
int       LinkNode_hasMemoryLeak();

#endif
