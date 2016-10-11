// linknode.h
#ifndef INCLUDED_LINKNODE
#define INCLUDED_LINKNODE

#include "Ilinknode.h"

class LinkNode : public ILinkNode {

  const void *d_key_p;
  const void *d_value_p;
  ILinkNode *d_next_p;

  // not implemented
  LinkNode(const LinkNode&);
  LinkNode& operator=(const LinkNode&);

  public:
  // constructor
  LinkNode(const void* key, const void* value):
    d_key_p(key), d_value_p(value), d_next_p(nullptr){};

  virtual ~LinkNode(){};

  // accessors
  virtual const void *key() const {return d_key_p;};
  virtual const void *val() const {return d_value_p;};
  virtual ILinkNode *next() const {return d_next_p;};

  // manipulators
  virtual void set(const void* value){d_value_p = value;};
  virtual void setNext(ILinkNode *next){d_next_p = next;};

};

#endif
