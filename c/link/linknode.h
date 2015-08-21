// linknode.h
#ifndef INCLUDED_LINKNODE
#define INCLUDED_LINKNODE

class LinkNode {

  const void *d_key_p;
  const void *d_value_p;
  LinkNode *d_next_p;

  // not implemented
  LinkNode(const LinkNode&);
  LinkNode& operator=(const LinkNode&);

  public:
  // constructor
  LinkNode(const void* key, const void* value): d_key_p(key), d_value_p(value),
                                                d_next_p(nullptr){};
  ~LinkNode(){};

  // accessors
  const void *key() const {return d_key_p;};
  const void *val() const {return d_value_p;};
  LinkNode *next() const {return d_next_p;};

  // manipulators
  void set(const void* value){d_value_p = value;};
  void setNext(LinkNode *next){d_next_p = next;};

};

#endif
