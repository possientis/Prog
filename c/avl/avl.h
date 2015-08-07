// avl.h
#ifndef INCLUDED_AVL
#define INCLUDED_AVL

class AVLNode;

class AVL {

  private:
  // private data
  bool (*d_comp_p)(void*,void*);  // strict comparison operator
  AVLNode *d_top_p;               // root node of AVL
  AVL(const AVL&);                // not implemented
  AVL& operator=(const AVL&);     // not implemented

  public:
  AVL(bool (*comp)(void*,void*));
  ~AVL();

  // accessors
  void* min(void* &key) const;              // returns value pointer and min key
  void* max(void* &key) const;              // returns value pointer and max key
  void* find(void* key) const;              // returns value associated with key
  void* succ(void* key, void*& succ) const; // returns successor value and key
  void* pred(void* key, void*& pred) const; // returns predecessor value and key
  bool check() const;                       // returns false if sanity checks fail
  void print(void (*func)(void *)) const;   // prints tree from key printing func

  // manipulators
  void insert(void* key, void* value);    // value changed on duplicate key
  void del(void* key);                    // has no impact unless key in tree

};

#endif
