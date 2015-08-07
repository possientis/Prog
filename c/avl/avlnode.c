// avlnode.c
#include "avlnode.h"
#include <assert.h>

struct AVLNode_i {

  void *key;
  void *value;
  int height;
  AVLNode *left;
  AVLNode *right;
  AVLNode *parent;

};


AVLNode::~AVLNode()
{
  assert(d_this != nullptr);
  delete d_this;
  d_this = nullptr;
}

AVLNode::AVLNode(void* key, void* value)
{

  d_this = new AVLNode_i();
  assert(d_this != nullptr);
  d_this->key = key;
  d_this->value = value;
  d_this->height = -1;
  d_this->left = nullptr;
  d_this->right = nullptr;
  d_this->parent = nullptr;

}

void* AVLNode::key() const
{
  return d_this->key;
}

void* AVLNode::val() const
{
  return d_this->value;
}

int AVLNode::height() const
{
  return d_this->height;
}

AVLNode* AVLNode::left() const
{
  return d_this->left;
}

AVLNode* AVLNode::right() const
{
  return d_this->right;
}

AVLNode* AVLNode::parent() const
{
  return d_this->parent;
}

void AVLNode::set(void* value)
{
  d_this->value = value;
}

void AVLNode::setHeight(int height)
{
  d_this->height = height;
}

void AVLNode::setLeft(AVLNode *left)
{
  d_this->left = left;
}

void AVLNode::setRight(AVLNode *right)
{
  d_this->right = right;
}

void AVLNode::setParent(AVLNode *parent)
{
  d_this->parent = parent;
}

