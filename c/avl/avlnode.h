// avlnode.h
#ifndef INCLUDED_AVLNODE
#define INCLUDED_AVLNODE

struct AVLNode_i;

class AVLNode {

  AVLNode_i *d_this;

  // not implemented
  AVLNode(const AVLNode&);
  AVLNode& operator=(const AVLNode&);

  public:
  // constructor
  AVLNode(void* key, void* value);
  ~AVLNode();

  // accessors
  void *key() const;
  void *val() const;
  int height() const;
  AVLNode *left() const;
  AVLNode *right() const;
  AVLNode *parent() const;

  // manipulators
  void set(void* value);
  void setHeight(int height);
  void setLeft(AVLNode *left);
  void setRight(AVLNode *right);
  void setParent(AVLNode *parent);

};


#endif
