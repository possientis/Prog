// link.c
#include "link.h"
#include "assert.h"
#include <stdio.h>

#ifndef INCLUDED_LINKNODE
#include "linknode.h"
#endif

// just to make code below more readable
typedef int (*Comparator)(const void*, const void*);  // == 0 on equality
typedef void (*PrintKeyFunc)(const void*);


static void freeNode(LinkNode *node){

  if(node != nullptr){

    freeNode(node->next());
    delete node;

  }

}


static LinkNode *insertNode(LinkNode *node,
    const void* key, const void* value, Comparator comp){

  if (node == nullptr){   // empty list

    node = new LinkNode(key,value);
    assert(node != nullptr);
    return node;

  }

  if (comp(key, node->key()) == 0){ // duplicate key

    node->set(value);
    return node;

  }

  // inserting from next node onwards
  LinkNode *next = node->next();
  node->setNext(insertNode(next,key,value,comp));
  return node;

}


static LinkNode *deleteNode(LinkNode *node, const void* key, Comparator comp){

  if(node == nullptr) return nullptr;   // nothing to do on empty list

  if(comp(key, node->key()) == 0){  // key found

    LinkNode *temp = node->next();  // head of list after deletion
    delete node;                    // release memory for head node
    node = nullptr;                 // safety
    return temp;

  }

  // deleting from next node onwards
  LinkNode *next = node->next();
  node->setNext(deleteNode(next,key,comp));
  return node;

}


static LinkNode *findNode(LinkNode *node, const void* key, Comparator comp){

  if (node == nullptr) return nullptr;  // search failing

  if(comp(key, node->key()) == 0){      // key found

    return node;

  }

  // search from next onwards
  return findNode(node->next(), key, comp);

}


static void printNode(const LinkNode *node, PrintKeyFunc func){

  if(node != nullptr){  // nothing printed otherwise

    func(node->key()); printf(" ");
    printNode(node->next(),func);

  }

}

// destructor
Link::~Link(){

  freeNode(d_head_p);

}


void Link::insert(const void* key, const void* value){

  d_head_p = insertNode(d_head_p,key,value,d_comp_p);   // new head after insert

}


void Link::del(const void* key){

  d_head_p = deleteNode(d_head_p, key, d_comp_p);  // new head after deletion

}


const void* Link::find(const void* key){

  LinkNode *temp = findNode(d_head_p, key, d_comp_p); // node with given key

  if(temp ==nullptr)  return nullptr;   // search failed

  return temp->val();                   // returning corresponding value pointer

}


void Link::print(PrintKeyFunc func) const{

  printf("( ");
  printNode(d_head_p, func);
  printf(")");

}


void LinkIter::operator++(){

  assert(d_node_p != nullptr);
  d_node_p = d_node_p->next();

}


const void* LinkIter::key() const{

  assert(d_node_p != nullptr);
  return d_node_p->key();

}

const void* LinkIter::val() const{

  assert(d_node_p != nullptr);
  return d_node_p->val();

}
