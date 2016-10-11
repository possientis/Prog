// linknode.t.c
#ifndef INCLUDED_LINKNODE
#include "linknode.h"
#endif

#include <stdio.h>

int linknode_test();

int main (int argc, char * argv[]){

 return linknode_test();

}

int linknode_test()
{

  printf("LinkNode: starting unit test\n");

  int k0 = 0;
  int k1 = 1;
  int k2 = 2;

  int v0 = 0;
  int v1 = 10;
  int v2 = 20;
  int v3 = 30;

  LinkNode a(&k0,&v0);
  LinkNode b(&k1,&v1);
  LinkNode c(&k2,&v2);
  //
  // checking keys
  if(a.key() != &k0) printf("LinkNode: unit test 1 failing\n");
  if(b.key() != &k1) printf("LinkNode: unit test 2 failing\n");
  if(c.key() != &k2) printf("LinkNode: unit test 3 failing\n");
  //
  // checking values
  if(a.val() != &v0) printf("LinkNode: unit test 4 failing\n");
  if(b.val() != &v1) printf("LinkNode: unit test 5 failing\n");
  if(c.val() != &v2) printf("LinkNode: unit test 6 failing\n");
  a.set(&v3);
  if(a.val() != &v3) printf("LinkNode: unit test 7 failing\n");
  //
  // checking next
  if(a.next() != nullptr) printf("LinkNode: unit test 8 failing\n");
  if(b.next() != nullptr) printf("LinkNode: unit test 9 failing\n");
  if(c.next() != nullptr) printf("LinkNode: unit test 10 failing\n");
  //
  // setNext
  a.setNext(&b);
  b.setNext(&c);
  c.setNext(&a);
  if(a.next() != &b) printf("LinkNode: unit test 11 failing\n");
  if(b.next() != &c) printf("LinkNode: unit test 12 failing\n");
  if(c.next() != &a) printf("LinkNode: unit test 13 failing\n");


  printf("LinkNode: unit test complete\n");

  return 0;

}
