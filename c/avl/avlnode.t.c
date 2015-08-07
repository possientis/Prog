// avlnode.t.c
#ifndef INCLUDED_AVLNODE
#include "avlnode.h"
#endif

#include <stdio.h>


int main(int argc, char * argv[]){

  int v0,v1,v2,v3;

  v0 = 0;
  v1 = 10;
  v2 = 20;
  v3 = 30;

  int k0,k1,k2;

  k0 = 0;
  k1 = 1;
  k2 = 2;

  AVLNode a(&k0, &v0);
  AVLNode b(&k1, &v1);
  AVLNode c(&k2, &v2);

  printf("AVLNode: starting unit test\n");

  // checking key()
  if(a.key() != &k0) printf("AVLNode: unit test 1 failing\n");
  if(b.key() != &k1) printf("AVLNode: unit test 2 failing\n");
  if(c.key() != &k2) printf("AVLNode: unit test 3 failing\n");

  // checking value()
  if(a.val() != &v0) printf("AVLNode: unit test 4 failing\n");
  if(b.val() != &v1) printf("AVLNode: unit test 5 failing\n");
  if(c.val() != &v2) printf("AVLNode: unit test 6 failing\n");
  a.set(&v3);
  if(a.val() != &v3) printf("AVLNode: unit test 7 failing\n");

  // checking left
  a.setLeft(&b);
  if(a.left() != &b) printf("AVLNode: unit test 8 failing\n");

  // checking right
  a.setRight(&c);
  if(a.right() != &c) printf("AVLNode: unit test 9 failing\n");

  // checking parent
  b.setParent(&a);
  c.setParent(&a);
  if(b.parent() != &a) printf("AVLNode: unit test 10 failing\n");
  if(c.parent() != &a) printf("AVLNode: unit test 11 failing\n");

  // checking height
  if (a.height() != -1) printf("AVLNode: unit test 12 failing\n");
  if (b.height() != -1) printf("AVLNode: unit test 13 failing\n");
  if (c.height() != -1) printf("AVLNode: unit test 14 failing\n");
  a.setHeight(1);
  b.setHeight(0);
  c.setHeight(0);
  if (a.height() != 1) printf("AVLNode: unit test 15 failing\n");
  if (b.height() != 0) printf("AVLNode: unit test 16 failing\n");
  if (c.height() != 0) printf("AVLNode: unit test 17 failing\n");


  printf("AVLNode: unit test complete\n");

  return 0;
}

