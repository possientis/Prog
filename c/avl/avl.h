// avl.h
#ifndef INCLUDED_AVL
#define INCLUDED_AVL

class AVLNode;

class AVL {

  private:
  // private data
  int (*d_comp_p)(const void*,const void*);   // comparison operator
  AVLNode *d_top_p;               // root node of AVL
  AVL(const AVL&);                // not implemented
  AVL& operator=(const AVL&);     // not implemented

  public:
  AVL(int (*comp)(const void*,const void*));
  ~AVL();

  // accessors
  const void* min(const void* *key_p) const;  // returns value pointer and min key
  const void* max(const void* *key_p) const;  // returns value pointer and max key
  const void* find(const void* key) const;  // returns value associated with key
  const void* succ(const void* key, const void* *succ_p) const;
  const void* pred(const void* key, const void* *pred_p) const;
  bool check() const;                       // returns false if sanity checks fail
  void print(void (*func)(const void *)) const;// prints tree from key print func

  // manipulators
  void insert(const void* key, const void* value);// val changed on duplicate key
  void del(const void* key);                // has no impact unless key in tree

};

#endif
