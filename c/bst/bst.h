// bst.h
#ifndef INCLUDED_BST
#define INCLUDED_BST

#ifndef INCLUDED_BSTNODE
#include "bstnode.h"
#endif

template <class Key, class T>

class BST {

  private:
  // private data
  bool (*d_comp_p)(Key,Key);  // strict comparison operator
  BSTNode<Key,T> *d_top_p;    // root node of BST
  BST(const BST&);            // not implemented
  BST& operator=(const BST&); // not implemented

  public:
  BST(bool (*comp)(Key,Key)): d_comp_p(comp), d_top_p(nullptr){}
  ~BST();

  // accessors
  T* min(Key& key) const;           // returns value pointer and minimal key
  T* max(Key& key) const;           // returns value pointer and maximal key
  T* find(Key key) const;           // returns value pointer of key, or nullptr
  T* succ(Key key, Key& succ) const;// returns successor value and key
  T* pred(Key key, Key& pred) const;// returns predecessor value and key
  bool check() const;               // returns false if sanity checks fail

  // manipulators
  void insert(Key key, T* value);   // value is simply changed on duplicate key
  void del(Key key);                // has no impact unless key in tree

};

// template implementation included in header file
#include "bst.c"

#endif
