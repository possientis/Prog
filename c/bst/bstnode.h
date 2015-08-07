// bstnode.h
#ifndef INCLUDED_BSTNODE
#define INCLUDED_BSTNODE

template <class Key, class T>
class BSTNode {
  //
  // private data
  Key d_key;
  T *d_value_p;
  BSTNode *d_left_p;
  BSTNode *d_right_p;
  BSTNode *d_parent_p;
  //
  // not implemented
  BSTNode(const BSTNode&);
  BSTNode& operator=(const BSTNode&);

  public:
  // constructor
  BSTNode(Key key, T* val_p): d_key(key), d_value_p (val_p){}
  ~BSTNode(){}

  // accessors
  Key key() const {return d_key;}
  T *val() const {return d_value_p;}
  BSTNode *left() const {return d_left_p;}
  BSTNode *right() const {return d_right_p;}
  BSTNode *parent() const {return d_parent_p;}

  // manipulators
  void set(T* val_p) {d_value_p = val_p;}
  void setLeft(BSTNode *left_p){d_left_p = left_p;}
  void setRight(BSTNode *right_p){d_right_p = right_p;}
  void setParent(BSTNode *parent_p){d_parent_p = parent_p;}

};


#endif
