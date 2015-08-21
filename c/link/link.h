// link.h
#ifndef INCLUDED_LINK
#define INCLUDED_LINK

class LinkNode;

class Link {

  // private data
  int (*d_comp_p)(const void*, const void*);  // comparison operator
  LinkNode *d_head_p;                         // head of linked list
  //
  Link(const Link&);                          // not implemented
  Link& operator=(const Link&);               // not implemented

  public:
  Link(int (*comp)(const void*,const void*)):d_comp_p(comp), d_head_p(nullptr){};
  ~Link();

  // accessors
  const void* find(const void* key);  // returns value associated with key
  bool isEmpty() const{return (d_head_p ==nullptr);};
  void print(void (*func)(const void*)) const;  // print keys from key print func


  // manipulators
  void insert(const void* key, const void* value); // val changed on duplicate key
  void del(const void* key);                       // no impact unless key in list

};



#endif
