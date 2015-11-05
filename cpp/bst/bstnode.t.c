// bstnode.t.c
#ifndef INCLUDED_BSTNODE
#include "bstnode.h"
#endif

#include <stdio.h>

struct T{

  int value;

};


int main(int argc, char * argv[]){

  T v0,v1,v2,v3;

  v0.value = 10;
  v1.value = 20;
  v2.value = 30;
  v3.value = 100;

  BSTNode<int,T> a(1, &v0);
  BSTNode<int,T> b(2, &v1);
  BSTNode<int,T> c(3, &v2);

  printf("BSTNode: starting unit test\n");

  // checking key()
  if(a.key() != 1) printf("BSTNode: unit test 1 failing\n");
  if(b.key() != 2) printf("BSTNode: unit test 2 failing\n");
  if(c.key() != 3) printf("BSTNode: unit test 3 failing\n");

  // checking value()
  if(a.val()->value != 10) printf("BSTNode: unit test 4 failing\n");
  if(b.val()->value != 20) printf("BSTNode: unit test 5 failing\n");
  if(c.val()->value != 30) printf("BSTNode: unit test 6 failing\n");
  a.set(&v3);
  if(a.val()->value != 100) printf("BSTNode: unit test 7 failing\n");

  // checking left
  a.setLeft(&b);
  if(a.left() != &b) printf("BSTNode: unit test 8 failing\n");

  // checking right
  a.setRight(&c);
  if(a.right() != &c) printf("BSTNode: unit test 9 failing\n");

  // checking parent
  b.setParent(&a);
  c.setParent(&a);
  if(b.parent() != &a) printf("BSTNode: unit test 10 failing\n");
  if(c.parent() != &a) printf("BSTNode: unit test 11 failing\n");


  printf("BSTNode: unit test complete\n");

  return 0;
}

