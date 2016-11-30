// avl.c
#include "avl.h"
#include <assert.h>
#include <stdio.h>

#ifndef INCLUDED_AVLNODE
#include "avlnode.h"
#endif


// just to make code below more readable
typedef int (*Comparator)(const void*, const void*);
typedef void (*PrintKeyFunc)(const void*);

static int height(const AVLNode *node){

  if(node == nullptr) return -1;

  return node->height();

}

static int leftHeight(const AVLNode *node){

  assert(node != nullptr);  // should not be called otherwise

  return height(node->left());

}


static int rightHeight(const AVLNode *node){

  assert(node != nullptr);  // should not be called otherwise

  return height(node->right());

}


static bool isBalanced(const AVLNode *node){

  assert(node != nullptr);  // should not be called otherwise

  int lh = leftHeight(node);
  int rh = rightHeight(node);

  if (lh > rh + 1) return false;
  if (rh > lh + 1) return false;
  return true;

}


static void updateHeight(AVLNode *node){

  assert(node != nullptr);  // should not be called otherwise

  int lh = leftHeight(node);
  int rh = rightHeight(node);
  int max = (lh > rh) ? lh : rh;

  node->setHeight(1 + max);

}


// root of right child promoted to root
static AVLNode* leftRotateNode(AVLNode *node){

  assert(node != nullptr);      // should not be called otherwise

  AVLNode* right = node->right();
  assert(right != nullptr);     // should no be called otherwise

  AVLNode* mid = right->left(); // left child of right child

  node->setRight(mid);          // new right child for node
  if(mid != nullptr) mid->setParent(node);
  updateHeight(node);           // re-calc height after change of child

  right->setLeft(node);         // new left child for right
  node->setParent(right);
  right->setParent(nullptr);    // right is now root
  updateHeight(right);          // re-calc height after change of child

  return right;

}


// root of left child promoted to root
static AVLNode* rightRotateNode(AVLNode *node){

  assert(node != nullptr);      // should not be called otherwise

  AVLNode* left = node->left();
  assert(left != nullptr);     // should no be called otherwise

  AVLNode* mid = left->right(); // right child of left child

  node->setLeft(mid);          // new left child for node
  if(mid != nullptr) mid->setParent(node);
  updateHeight(node);           // re-calc height after change of child

  left->setRight(node);         // new right child for left
  node->setParent(left);
  left->setParent(nullptr);     // left is now root
  updateHeight(left);           // re-calc height after change of child

  return left;

}



// restores AVL property when node is right-heavy
static AVLNode* rightRebalanceNode(AVLNode *node){

  assert(node != nullptr);     // should not be called otherwise

  AVLNode *right = node->right();
  assert(right != nullptr);    // should not be called otherwise

  if(leftHeight(right) > rightHeight(right)){ // more rebalancing needed

    AVLNode *temp = rightRotateNode(right);
    node->setRight(temp);   // new right child for node
    temp->setParent(node);  // corresponding parent link
    updateHeight(node);     // re-calc height after change of child

  }

  return leftRotateNode(node);

}


// restores AVL property when node is left-heavy
static AVLNode* leftRebalanceNode(AVLNode *node){

  assert(node != nullptr);     // should not be called otherwise

  AVLNode *left = node->left();
  assert(left != nullptr);    // should not be called otherwise

  if(rightHeight(left) > leftHeight(left)){ // more rebalancing needed

    AVLNode *temp = leftRotateNode(left);
    node->setLeft(temp);   // new left child for node
    temp->setParent(node);  // corresponding parent link
    updateHeight(node);     // re-calc height after change of child

  }

  return rightRotateNode(node);

}


static AVLNode* rebalanceNode(AVLNode *node){

  assert(node != nullptr);    // should not be called otherwise

  if(isBalanced(node)) return node;
  if(leftHeight(node) < rightHeight(node)) return rightRebalanceNode(node);
  if(rightHeight(node) < leftHeight(node)) return leftRebalanceNode(node);

  // should not reach this point

  assert(false);

}


static void freeNode(AVLNode *node){

  if(node != nullptr){      // nothing to do if tree empty

    freeNode(node->left()); // free nodes of left child
    freeNode(node->right());// free nodes of right child

    delete node;
  }

}


static AVLNode *insertNode(AVLNode *node,
    const void* key, const void *value,Comparator comp){

  if (node == nullptr){  // tree is empty

    node =  new AVLNode(key,value);
    assert(node != nullptr);
    node->setHeight(0);
    return node;

  }

  if(comp(key,node->key()) < 0){ // key is to the left
    node->setLeft(insertNode(node->left(),key,value,comp)); // insert left
    node->left()->setParent(node);  // connecting to parent
    updateHeight(node); // re-calculating node height after change
    return rebalanceNode(node);
  }

  if(comp(node->key(),key) < 0){  // key is to the right
    node->setRight(insertNode(node->right(),key,value,comp));// right
    node->right()->setParent(node); // connecting to parent
    updateHeight(node); // re-calculating node height after change
    return rebalanceNode(node);  // returning initial node following update
  }

  node->set(value); // < and > have failed: duplicate keys
  return node;  // returning initial node with new value

}

// restructure the tree so as to bring the min node to root
static AVLNode *rootMinNode(AVLNode *node){

  if(node == nullptr) return nullptr; // no impact on empty tree

  if(node->left() == nullptr){ // no left child, min node already root
    node->setParent(nullptr); // returning a root node
    return node;
  }
  else {  // left child does exist
    AVLNode *temp = rootMinNode(node->left());  // recursive call
    node->setLeft(temp->right()); // new left child without the min
    if(node->left() != nullptr) node->left()->setParent(node);
    updateHeight(node);     // re-calc height after change of child
    temp->setRight(node);   // node getting to the right of min
    node->setParent(temp);  // not forgetting parent link
    updateHeight(temp);     // re-calc height after change of child
    return temp;            // returning min node
  }

}


static AVLNode *rootMaxNode(AVLNode *node){

  if(node == nullptr) return nullptr; // no impact on empty tree

  if(node->right() == nullptr){ // no right child, max node already root
    node->setParent(nullptr); // returning a root node
    return node;
  }
  else {  // right child does exist
    AVLNode *temp = rootMaxNode(node->right());  // recursive call
    node->setRight(temp->left()); // new right child without the max
    if(node->right() != nullptr) node->right()->setParent(node);
    updateHeight(node);     // re-calc height after change of child
    temp->setLeft(node);  // node getting to the left of max
    node->setParent(temp);  // not forgetting parent link
    updateHeight(temp);     // re-calc height after change of child
    return temp;  // returning max node
  }

}


static AVLNode *deleteNode(AVLNode *node, const void* key, Comparator comp){

  if(node == nullptr) return nullptr;   // nothing to do on empty tree

  if(comp(key,node->key()) < 0){  // key is to the left
    AVLNode *temp = deleteNode(node->left(),key, comp);// left delete
    node->setLeft(temp);  // linking new left child
    if(temp != nullptr) temp->setParent(node); // parent link if applicable
    updateHeight(node);     // re-calc height after change of child
    return rebalanceNode(node);  // return original node after modification
  }

  if(comp(node->key(),key) < 0){  // key is to the right
    AVLNode *temp = deleteNode(node->right(),key,comp);//right delete
    node->setRight(temp);  // linking new right child
    if(temp != nullptr) temp->setParent(node); // parent link if applicable
    updateHeight(node);     // re-calc height after change of child
    return rebalanceNode(node);  // return original node after modification
  }

  // key to be deleted is equal to node key
  if(node->left() == nullptr){  // left child does not exist
    AVLNode *temp = node->right(); //  candidate for tree after deletion
    if(temp != nullptr) temp->setParent(nullptr); // new root
    delete node; // just free memory for root node which is deleted
    node = nullptr; // for safety reasons
    return temp;
  }

  if(node->right() == nullptr){ // left child does exist, but not right child
    AVLNode *temp = node->left();
    temp->setParent(nullptr); // no need to check for null pointer now
    delete node;  // just free memory for root node which is deleted
    node = nullptr; // for safety reasons
    return temp;
  }

  // both left and right child exist, while root needs to be deleted
  // we arbitrarily choose to promote successor as new root

  AVLNode *temp = rootMinNode(node->right());
  temp->setLeft(node->left());  // gluing initial left child
  temp->left()->setParent(temp);  // not forgetting parent link
  updateHeight(temp); // re-calc height after change of child
  delete node;  // just free memory for root node which is deleted
  node = nullptr; // for safety reasons
  return rebalanceNode(temp);

}


static AVLNode *minNode(AVLNode *node){

  if(node == nullptr) return nullptr;
  if(node->left() == nullptr) return node;  // no left child, node is min
  return minNode(node->left()); // minimal key in left child
}



static AVLNode *maxNode(AVLNode *node){

  if(node == nullptr) return nullptr;
  if(node->right() == nullptr) return node; // no right child, node is max
  return maxNode(node->right());  // maximal key in right child
}



static AVLNode *findNode(AVLNode *node, const void* key, Comparator comp){

  if(node == nullptr) return nullptr;

  if(comp(key,node->key()) < 0){  // key is to the left
    return findNode(node->left(),key, comp);  // finding left child
  }

  if(comp(node->key(),key) < 0){  // key is to the right
    return findNode(node->right(),key,comp); // finding right child
  }

  return node;  // < and > have failed, key found
}



static AVLNode *succNode(AVLNode *node, const void* key, Comparator comp){

  if(node == nullptr) return nullptr; // key has no successor in tree

  if(comp(key,node->key()) < 0){ // key is to the left
    AVLNode *temp = succNode(node->left(),key,comp);  // looking left
    if(temp == nullptr)
    { // there is no successor of key in left child
      return node;  // current node has successor key
    }
    else
    {
      return temp;  // successor of key in left child is successor key
    }
  }

  if(comp(node->key(),key) < 0){ // key is to the right, if successor exists ...
    return succNode(node->right(),key,comp); // ... it must be on the right
  }

  // both < and > have failed, key is equal to key of current node
  if (node->right() == nullptr)
  {  // right child does not exist
    AVLNode *parent = node->parent();     // successor possibly parent
    if(parent == nullptr) return nullptr; // no parent then no succ
    if(comp(key,parent->key()) < 0)
    {  // parent key greater, it is successor
      return parent;
    }
    else
    {  // parent key cannot be equal, hence it is smaller and no successor
      return nullptr;
    }
  } // right child does not exist
  else
  { // right child does exist
    return minNode(node->right());  // successor is min of right child
  }
}



static AVLNode *predNode(AVLNode *node, const void* key, Comparator comp){

  if(node == nullptr) return nullptr; // key has no predecessor in tree

  if(comp(node->key(),key) < 0){ // key is to the right
    AVLNode *temp = predNode(node->right(),key,comp);  // looking right
    if(temp == nullptr)
    {  // there is no predecessor of key in right child
      return node;  // current node has predecessor key
    }
    else
    {
      return temp;  // predecessor of key in right child is predecessor key
    }
  }

  if(comp(key,node->key()) < 0){ // key is to the left, if predecessor exists ..
    return predNode(node->left(),key,comp); // ... it must be on the left
  }

  // both < and > have failed, key is equal to key of current node
  if (node->left() == nullptr)
  {  // left child does not exist
    AVLNode *parent_p = node->parent();  // predecessor possibly parent
    if(parent_p == nullptr){  // if no parent then no predecessor
      return nullptr;
    }
    if(comp(parent_p->key(), key) < 0)
    {  // parent key smaller, it is predecessor
      return parent_p;
    }
    else
    {  // parent key cannot be equal, hence it is greater and no predecessor
      return nullptr;
    }
  } // left child does not exist
  else
  { // left child does exist
    return maxNode(node->left());  // predecessor is max of left child
  }
}


// checks AVL invariant
static bool checkAVLNode(const AVLNode *node){

  if (node == nullptr) return true; // AVL invariant satisfied

  if(!checkAVLNode(node->left())) return false; // failure left
  if(!checkAVLNode(node->right())) return false;// failure right

  return isBalanced(node);

}

// checks calculated heights values
static bool checkHeightNode(const AVLNode *node){

  if (node == nullptr) return true; // no stale height on empty tree

  if(!checkHeightNode(node->left())) return false;  // failure left
  if(!checkHeightNode(node->right())) return false; // failure right

  int lh = leftHeight(node);
  int rh = rightHeight(node);
  int max = (lh > rh) ? lh : rh;

  return (node->height() == (1 + max));

}



// checks BST invariant
static bool checkBSTNode(const AVLNode *node, Comparator comp){

  if(node == nullptr) return true;  // empty tree satisfies invariant

  if(!checkBSTNode(node->left(), comp)) return false; // failure left

  if(!checkBSTNode(node->right(), comp)) return false;// failure right

  if(node->left() != nullptr){  // left child exists

    const void* key = maxNode(node->left())->key(); // maximal key in left child

    if(comp(key,node->key()) >= 0){ // left maximal key is not smaller

      return false; // binary search tree property is violated

    }

  }

  if(node->right() != nullptr){ // right child exists

    const void* key = minNode(node->right())->key(); // minimal key in right child

    if(comp(node->key(),key) >= 0){ // right minimal key is not greater

      return false; // binary search tree property is violated

    }

  }

  return true;  // all tests were successful

}


// checks parent links
static bool checkParentNode(const AVLNode *node){

  if(node == nullptr) return true;  // empty tree nothing to check

  if(!checkParentNode(node->left())) return false;  // checking left
  if(!checkParentNode(node->right())) return false; // checking right

  if(node->left() != nullptr){  // left child exists
    if(node->left()->parent() != node){ // parent of child is not node
      return false;
    }
  }

  if(node->right() != nullptr){ // right child exists
    if(node->right()->parent() != node){ // parent of child is not node
      return false;
    }
  }

  return true;  // all tests were successful

}


static void printNode(const AVLNode *node, PrintKeyFunc func){

  if(node == nullptr)
  {
    printf(".");
  }
  else
  {
    printf("(");
    func(node->key()); printf(" ");
    printNode(node->left(),func); printf(" ");
    printNode(node->right(),func);
    printf(")");
  }

}



// public interface implementation

AVL::AVL(Comparator comp): d_comp_p(comp), d_top_p(nullptr){}

AVL::~AVL(){

  freeNode(d_top_p);
}

void AVL::print(PrintKeyFunc func) const{

  printNode(d_top_p,func);

}


void AVL::insert(const void* key, const void* value){

  d_top_p = insertNode(d_top_p, key, value, d_comp_p);  // new root after insert

}


void AVL::del(const void* key){

  d_top_p = deleteNode(d_top_p, key, d_comp_p); // new root node after deletion

}


const void* AVL::min(const void* *key_p) const{

  assert(key_p != nullptr);

  AVLNode *temp = minNode(d_top_p);  // node with minimal key

  if(temp == nullptr) return nullptr; // tree is empty

  *key_p = temp->key();  // returning minimal key

  return temp->val(); // returning corresponding value pointer

}


const void* AVL::max(const void* *key_p) const{

  assert(key_p != nullptr);

  AVLNode *temp = maxNode(d_top_p);  // node with maximal key

  if(temp == nullptr) return nullptr; // tree is empty

  *key_p = temp->key();  // returning maximal key

  return temp->val(); // returning corresponding value pointer

}


const void* AVL::find(const void* key) const{

  AVLNode *temp = findNode(d_top_p, key, d_comp_p);  // node with given key

  if(temp == nullptr) return nullptr; // find failed

  return temp->val();   // returning corresponding value pointer

}


const void* AVL::succ(const void* key, const void* *succ_p) const{

  assert(succ_p != nullptr);

  AVLNode *temp = succNode(d_top_p, key, d_comp_p);  // node with succ key

  if(temp == nullptr) return nullptr;   // no successor

  *succ_p = temp->key(); // returning successor key

  return temp->val(); // returning corresponding value pointer

}


const void* AVL::pred(const void* key, const void* *pred_p) const{

  assert(pred_p != nullptr);

  AVLNode *temp = predNode(d_top_p, key, d_comp_p);  // node with pred key

  if(temp == nullptr) return nullptr;   // no predecessor

  *pred_p = temp->key(); // returning predecessor key

  return temp->val(); // returning corresponding value pointer

}


bool AVL::check() const{

  // checking BST invariant
  if(!checkBSTNode(d_top_p, d_comp_p)) return false;

  // checking parent links
  if(!checkParentNode(d_top_p)) return false;

  // checking calculated heights
  if(!checkHeightNode(d_top_p)) return false;

  // checking AVL invariant
  if(!checkAVLNode(d_top_p)) return false;

  // root node should have no parent
  if(d_top_p != nullptr){

    if(d_top_p->parent() != nullptr) return false;

  }

  return true;  // all tests passed successfully

}

