// link.h
#ifndef INCLUDED_LINK
#define INCLUDED_LINK

class LinkNode;
class LinkIter;

class Link {

  // private data
  int (*d_comp_p)(const void*, const void*);  // comparison operator
  LinkNode *d_head_p;                         // head of linked list
  //
  Link(const Link&);                          // not implemented
  Link& operator=(const Link&);               // not implemented

  //friends
  friend LinkIter;

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

class LinkIter {

  // private data
  LinkNode *d_node_p;
  //
  LinkIter(const LinkIter&);                  // not implemented
  LinkIter& operator=(const LinkIter&);       // not implemented

  public:
  LinkIter(const Link& link):d_node_p(link.d_head_p){};
  ~LinkIter(){};

  // manipulator
  void operator++();                          // pre-increment

  // accessors
  operator const void*() const {return d_node_p;};
  const void* key() const;
  const void* val() const;

};


#endif
