// bst.h
#ifndef INCLUDED_BST
#define INCLUDED_BST

#ifndef INCLUDED_BSTNODE
#include "bstnode.h"
#endif

#include <assert.h>

template <class Key, class T>

class BST {

  private:
  // private data
  int (*d_comp_p)(Key,Key);  // strict comparison operator
  BSTNode<Key,T> *d_top_p;    // root node of BST
  BST(const BST&);            // not implemented
  BST& operator=(const BST&); // not implemented

  public:
  BST(int (*comp)(Key,Key)): d_comp_p(comp), d_top_p(nullptr){}
  ~BST();

  // accessors
  const T* min(Key* key) const;     // returns value pointer and minimal key
  const T* max(Key* key) const;     // returns value pointer and maximal key
  const T* find(Key key) const;     // returns value pointer of key, or nullptr
  const T* succ(Key key, Key* succ) const;// returns successor value and key
  const T* pred(Key key, Key* pred) const;// returns predecessor value and key
  bool check() const;               // returns false if sanity checks fail

  // manipulators
  void insert(Key key, const T* value);// value is simply changed on duplicate key
  void del(Key key);                // has no impact unless key in tree

};

// template implementation included in header file
template <class Key, class T>

BST<Key,T>::~BST(){

  freeNode(d_top_p);
}

template <class Key, class T>

void BST<Key,T>::insert(Key key, const T* value_p){

  d_top_p = insertNode(d_top_p, key, value_p, d_comp_p);  // new root after insert

}

template <class Key, class T>

void BST<Key,T>::del(Key key){

  d_top_p = deleteNode(d_top_p, key, d_comp_p); // update top node after deletion

}


template <class Key, class T>

const T* BST<Key,T>::min(Key* key_p) const{


  assert(key_p != nullptr);

  const BSTNode<Key,T> *temp = minNode(d_top_p);  // node with minimal key

  if(temp == nullptr) return nullptr; // tree is empty

  *key_p = temp->key();  // returning minimal key

  return temp->val(); // returning corresponding value pointer

}


template <class Key, class T>

const T* BST<Key,T>::max(Key* key_p) const{

  assert(key_p != nullptr);

  const BSTNode<Key,T> *temp = maxNode(d_top_p);  // node with maximal key

  if(temp == nullptr) return nullptr; // tree is empty

  *key_p = temp->key();  // returning maximal key

  return temp->val(); // returning corresponding value pointer

}


template <class Key, class T>

const T* BST<Key,T>::find(Key key) const{

  // node with given key
  const BSTNode<Key,T> *temp = findNode(d_top_p, key, d_comp_p);


  if(temp == nullptr) return nullptr; // find failed

  return temp->val();   // returning corresponding value pointer

}


template <class Key, class T>

const T* BST<Key,T>::succ(Key key, Key* succ_p) const{

  //
  assert(succ_p != nullptr);

  // node with succ key
  const BSTNode<Key,T> *temp = succNode(d_top_p, key, d_comp_p);

  if(temp == nullptr) return nullptr;   // no successor

  *succ_p = temp->key(); // returning successor key

  return temp->val(); // returning corresponding value pointer

}


template <class Key, class T>

const T* BST<Key,T>::pred(Key key, Key* pred_p) const{

  //
  assert(pred_p != nullptr);

  // node with pred key
  const BSTNode<Key,T> *temp = predNode(d_top_p, key, d_comp_p);

  if(temp == nullptr) return nullptr;   // no predecessor

  *pred_p = temp->key(); // returning predecessor key

  return temp->val(); // returning corresponding value pointer

}


template <class Key, class T>

bool BST<Key,T>::check() const{

  if(checkInvariantNode(d_top_p, d_comp_p) == false){

    return false; // binary search tree invariant not met

  }

  if(checkParentNode(d_top_p) == false){

    return false; // some parent pointer badly set

  }

  if(d_top_p != nullptr){ // if tree not empty

    if(d_top_p->parent() != nullptr){

      return false; // top node should not have parent

    }

  }

  return true;  // all tests passed successfully

}


template <class Key, class T>

static void freeNode(BSTNode<Key,T> *node_p){

  if(node_p != nullptr){    // nothing to do if tree empty

  freeNode(node_p->left()); // free nodes of left child

  freeNode(node_p->right());// free nodes of right child

  delete node_p;

  }
}


template <class Key, class T>

static BSTNode<Key,T> *insertNode(

  BSTNode<Key,T> *node_p, Key key, const T *value_p, int (*comp_p)(Key,Key)){



  if (node_p == nullptr){ // tree is empty

    return new BSTNode<Key,T>(key,value_p);

  }

  if(comp_p(key,node_p->key()) < 0){  // key is to the left

    node_p->setLeft(insertNode(node_p->left(),key,value_p,comp_p)); // insert left

    node_p->left()->setParent(node_p);  // connecting to parent

    return node_p;  // returning initial node following update

  }

  if(comp_p(node_p->key(),key) < 0){  // key is to the right

    node_p->setRight(insertNode(node_p->right(),key,value_p,comp_p));// right

    node_p->right()->setParent(node_p); // connecting to parent

    return node_p;  // returning initial node following update

  }

  node_p->set(value_p); // < and > have failed: duplicate keys

  return node_p;  // returning initial node with new value

}


template <class Key, class T>

static BSTNode<Key,T> *rootMinNode(BSTNode<Key,T> *node_p){

  if(node_p == nullptr) return nullptr; // no impact on empty tree

  if(node_p->left() == nullptr){ // no left child, min node already root

    node_p->setParent(nullptr); // returning a root node

    return node_p;

  }

  else {  // left child does exist

    BSTNode<Key,T> *temp = rootMinNode(node_p->left());  // recursive call

    node_p->setLeft(temp->right()); // new left child without the min

    if(node_p->left() != nullptr){ // if new left child exists ...

      node_p->left()->setParent(node_p); // ... setting up its parent

    }

    temp->setRight(node_p);  // node getting to the right of min

    node_p->setParent(temp);  // not forgetting parent link

    return temp;  // returning min node

  }

}



template <class Key, class T>

static BSTNode<Key,T> *rootMaxNode(BSTNode<Key,T> *node_p){

  if(node_p == nullptr) return nullptr; // no impact on empty tree

  if(node_p->right() == nullptr){ // no right child, max node already root

    node_p->setParent(nullptr); // returning a root node

    return node_p;

  }

  else {  // right child does exist

    BSTNode<Key,T> *temp = rootMaxNode(node_p->right());  // recursive call

    node_p->setRight(temp->left()); // new right child without the max

    if(node_p->right() != nullptr){ // if new right child exists ...

      node_p->right()->setParent(node_p); // ... setting up its parent

    }

    temp->setLeft(node_p);  // node getting to the left of max

    node_p->setParent(temp);  // not forgetting parent link

    return temp;  // returning max node

  }

}


template <class Key, class T>

static BSTNode<Key,T> *deleteNode(
    BSTNode<Key,T> *node_p, Key key, int (*comp_p)(Key,Key)){

  if(node_p == nullptr) return nullptr;   // nothing to do on empty tree

  if(comp_p(key,node_p->key()) < 0){  // key is to the left

    BSTNode<Key,T> *temp = deleteNode(node_p->left(),key, comp_p);// left delete

    node_p->setLeft(temp);  // linking new left child

   if(temp != nullptr) temp->setParent(node_p); // parent link if applicable

  return node_p;  // return original node after modification

  }

  if(comp_p(node_p->key(),key) < 0){  // key is to thr right

    BSTNode<Key,T> *temp = deleteNode(node_p->right(),key,comp_p);//right delete

    node_p->setRight(temp);  // linking new right child

   if(temp != nullptr) temp->setParent(node_p); // parent link if applicable

  return node_p;  // return original node after modification

  }

  // key to be deleted is equal to node key

  if(node_p->left() == nullptr){  // left child does not exist

    BSTNode<Key,T> *temp = node_p->right(); //  candidate for tree after deletion

    if(temp != nullptr) temp->setParent(nullptr); // new root

    delete node_p; // just free memory for root node which is deleted

    return temp;

  }

  if(node_p->right() == nullptr){ // left child does exist, but not right child

    BSTNode<Key,T> *temp = node_p->left();

    temp->setParent(nullptr); // no need to check for null pointer now

    delete node_p;  // just free memory for root node which is deleted

    return temp;

  }

  // both left and right child exist, while root needs to be deleted
  // we arbitrarily choose to promote successor as new root

  BSTNode<Key,T> *temp = rootMinNode(node_p->right());

  temp->setLeft(node_p->left());  // gluing initial left child

  temp->left()->setParent(temp);  // not forgetting parent link

  delete node_p;  // just free memory for root node which is deleted

  return temp;

}


template <class Key, class T>

static const BSTNode<Key,T> *minNode(const BSTNode<Key,T> *node_p){

  if(node_p == nullptr){  // tree is empty

    return nullptr;

  }

  if(node_p->left() == nullptr){ // no left child, top node minimal

    return node_p;

  }

  return minNode(node_p->left()); // minimal key in left child

}


template <class Key, class T>

static const BSTNode<Key,T> *maxNode(const BSTNode<Key,T> *node_p){

  if(node_p == nullptr){  // tree is empty

    return nullptr;

  }

  if(node_p->right() == nullptr){ // no right child, top node maximal

    return node_p;

  }

  return maxNode(node_p->right());  // maximal key in right child

}


template <class Key, class T>

static const BSTNode<Key,T> *findNode(
    const BSTNode<Key,T> *node_p, Key key, int (*comp_p)(Key,Key)){

  if(node_p == nullptr){  // tree empty

    return nullptr;

  }

  if(comp_p(key,node_p->key()) < 0){  // key is to the left

    return findNode(node_p->left(),key, comp_p);  // finding left child

  }

  if(comp_p(node_p->key(),key) < 0){  // key is to the right

    return findNode(node_p->right(),key,comp_p); // finding right child

  }

  return node_p;  // < and > have failed, key found

}


template <class Key, class T>

static const BSTNode<Key,T> *succNode(
    const BSTNode<Key,T> *node_p, Key key, int (*comp_p)(Key,Key)){

  if(node_p == nullptr){  // tree empty

    return nullptr; // key has no successor in tree

  }

  if(comp_p(key,node_p->key()) < 0){ // key is to the left

    const BSTNode<Key,T> *temp = succNode(node_p->left(),key,comp_p);//look left

    if(temp == nullptr){  // there is no successor of key in left child

      return node_p;  // current node has successor key

    }
    else {

      return temp;  // successor of key in left child is successor key

    }

  }

  if(comp_p(node_p->key(),key) < 0){ // key is to the right, if successor exists ...

    return succNode(node_p->right(),key,comp_p); // ... it must be on the right

  }

  // both < and > have failed, key is equal to key of current node

  if (node_p->right() == nullptr){  // right child does not exist

    BSTNode<Key,T> *parent_p = node_p->parent();  // successor possibly parent

    if(parent_p == nullptr){  // if no parent then no successor

      return nullptr;

    }

    if(comp_p(key,parent_p->key()) < 0){  // parent key greater, it is successor

      return parent_p;

    }

    else {  // parent key cannot be equal, hence it is smaller and no successor

      return nullptr;

    }

  } // right child does not exist

  else { // right child does exist

    return minNode(node_p->right());  // successor is min of right child

  }

}


template <class Key, class T>

static const BSTNode<Key,T> *predNode(
    const BSTNode<Key,T> *node_p, Key key, int (*comp_p)(Key,Key)){

  if(node_p == nullptr){  // tree empty

    return nullptr; // key has no predecessor in tree

  }

  if(comp_p(node_p->key(),key) < 0){ // key is to the right

    const BSTNode<Key,T> *temp = predNode(node_p->right(),key,comp_p);//look right

    if(temp == nullptr){  // there is no predecessor of key in right child

      return node_p;  // current node has predecessor key

    }
    else {

      return temp;  // predecessor of key in right child is predecessor key

    }

  }

  if(comp_p(key,node_p->key()) < 0){ // key is to the left, if predecessor exists ..

    return predNode(node_p->left(),key,comp_p); // ... it must be on the left

  }

  // both < and > have failed, key is equal to key of current node

  if (node_p->left() == nullptr){  // left child does not exist

    BSTNode<Key,T> *parent_p = node_p->parent();  // predecessor possibly parent

    if(parent_p == nullptr){  // if no parent then no predecessor

      return nullptr;

    }

    if(comp_p(parent_p->key(), key) < 0){  // parent key smaller, it is predecessor

      return parent_p;

    }

    else {  // parent key cannot be equal, hence it is greater and no predecessor

      return nullptr;

    }

  } // left child does not exist

  else { // left child does exist

    return maxNode(node_p->left());  // predecessor is max of left child

  }

}


template <class Key, class T>

static bool checkInvariantNode(
    const BSTNode<Key,T> *node_p, int (*comp_p)(Key,Key)){

  if(node_p == nullptr) return true;  // empty tree satisfies invariant

  if(!checkInvariantNode(node_p->left(), comp_p)) return false; // failure left

  if(!checkInvariantNode(node_p->right(), comp_p)) return false;// failure right

  if(node_p->left() != nullptr){  // left child exists

    Key key = maxNode(node_p->left())->key(); // maximal key in left child

    if(!comp_p(key,node_p->key())){ // left maximal key is not smaller

      return false; // binary search tree property is violated

    }

  }

  if(node_p->right() != nullptr){ // right child exists

    Key key = minNode(node_p->right())->key(); // minimal key in right child

    if(!comp_p(node_p->key(),key)){ // right minimal key is not greater

      return false; // binary search tree property is violated

    }

  }

  return true;  // all tests were successful

}


template <class Key, class T>

static bool checkParentNode(const BSTNode<Key,T> *node_p){

   if(node_p == nullptr) return true;  // empty tree nothing to check

  if(!checkParentNode(node_p->left())) return false;  // checking left

  if(!checkParentNode(node_p->right())) return false; // checking right

  if(node_p->left() != nullptr){  // left child exists

    if(node_p->left()->parent() != node_p){ // parent of child is not node

      return false;

    }

  }

  if(node_p->right() != nullptr){ // right child exists

    if(node_p->right()->parent() != node_p){ // parent of child is not node

      return false;

    }

  }

  return true;  // all tests were successful

}


#endif
