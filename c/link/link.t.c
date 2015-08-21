// link.t.c
#ifndef INCLUDED_LINK
#include "link.h"
#endif

#include <stdio.h>

static void printKey(const void* k)
{
  int key = *(int*) k;
  printf("%d",key);

}

static int comp1(const void* x, const void* y)
{
  int u = *(int*) x;
  int v = *(int*) y;

  return (u - v);

}

static int comp2(const void* x, const void* y)
{
  int u = *(int*) x;
  int v = *(int*) y;

  return (v - u);

}

int link_test();

int main(int argc, char * argv[]){

  return link_test();

}


int link_test(){

  printf("Link: starting unit test\n");

  int k0 = 0;
  int k1 = 1;
  int k2 = 2;
  int k3 = 3;
  int k5 = 5;
  int k7 = 7;
  int k8 = 8;

  int v0 = 0;
  int v1 = 10;
  int v2 = 20;
  int v3 = 30;
  int v5 = 50;
  int v8 = 80;
  int v10 = 100;
  int v20 = 200;

  Link a(comp1);
  Link b(comp2);



  if(!a.isEmpty()) printf("Link: unit test 1 failing\n");
  if(!b.isEmpty()) printf("Link: unit test 2 failing\n");

  // first insert
  a.insert(&k1,&v1);
  b.insert(&k2,&v2);
  if(a.isEmpty()) printf("Link: unit test 3 failing\n");
  if(b.isEmpty()) printf("Link: unit test 4 failing\n");
  if(a.find(&k0) != nullptr) printf("Link: unit test 1 failing\n");
  if(a.find(&k1) != &v1) printf("Link: unit test 5 failing\n");
  if(b.find(&k2) != &v2) printf("Link: unit test 6 failing\n");
  // second insert
  a.insert(&k3,&v3);
  b.insert(&k3,&v3);
  if(a.find(&k0) != nullptr) printf("Link: unit test 7 failing\n");
  if(a.find(&k1) != &v1) printf("Link: unit test 8 failing\n");
  if(b.find(&k2) != &v2) printf("Link: unit test 9 failing\n");
  if(a.find(&k3) != &v3) printf("Link: unit test 10 failing\n");
  if(b.find(&k3) != &v3) printf("Link: unit test 11 failing\n");
  // third insert (duplicate keys)
  a.insert(&k1,&v10);
  b.insert(&k2,&v20);
  if(a.find(&k0) != nullptr) printf("Link: unit test 12 failing\n");
  if(a.find(&k1) != &v10) printf("Link: unit test 13 failing\n");
  if(b.find(&k2) != &v20) printf("Link: unit test 14 failing\n");
  if(a.find(&k3) != &v3) printf("Link: unit test 15 failing\n");
  if(b.find(&k3) != &v3) printf("Link: unit test 16 failing\n");
  // fourth insert
  a.insert(&k5,&v5);
  b.insert(&k5,&v5);
  if(a.find(&k0) != nullptr) printf("Link: unit test 17 failing\n");
  if(a.find(&k1) != &v10) printf("Link: unit test 18 failing\n");
  if(b.find(&k2) != &v20) printf("Link: unit test 19 failing\n");
  if(a.find(&k3) != &v3) printf("Link: unit test 20 failing\n");
  if(b.find(&k3) != &v3) printf("Link: unit test 21 failing\n");
  if(a.find(&k5) != &v5) printf("Link: unit test 22 failing\n");
  if(b.find(&k5) != &v5) printf("Link: unit test 23 failing\n");
  // fifth insert
  a.insert(&k8,&v8);
  b.insert(&k8,&v8);
  if(a.find(&k0) != nullptr) printf("Link: unit test 24 failing\n");
  if(a.find(&k1) != &v10) printf("Link: unit test 25 failing\n");
  if(b.find(&k2) != &v20) printf("Link: unit test 26 failing\n");
  if(a.find(&k3) != &v3) printf("Link: unit test 27 failing\n");
  if(b.find(&k3) != &v3) printf("Link: unit test 28 failing\n");
  if(a.find(&k5) != &v5) printf("Link: unit test 29 failing\n");
  if(b.find(&k5) != &v5) printf("Link: unit test 30 failing\n");
  if(a.find(&k8) != &v8) printf("Link: unit test 31 failing\n");
  if(b.find(&k8) != &v8) printf("Link: unit test 32 failing\n");
  // first delete
  a.del(&k3);
  b.del(&k3);
  if(a.find(&k3) != nullptr) printf("Link: unit test 33 failing\n");
  if(b.find(&k3) != nullptr) printf("Link: unit test 34 failing\n");
  if(a.find(&k1) != &v10) printf("Link: unit test 35 failing\n");
  if(b.find(&k2) != &v20) printf("Link: unit test 36 failing\n");
  if(a.find(&k5) != &v5) printf("Link: unit test 37 failing\n");
  if(b.find(&k5) != &v5) printf("Link: unit test 38 failing\n");
  if(a.find(&k8) != &v8) printf("Link: unit test 39 failing\n");
  if(b.find(&k8) != &v8) printf("Link: unit test 40 failing\n");
  // second delete (absent key)
  a.del(&k7);
  b.del(&k7);
  if(a.find(&k0) != nullptr) printf("Link: unit test 41 failing\n");
  if(b.find(&k0) != nullptr) printf("Link: unit test 42 failing\n");
  if(a.find(&k1) != &v10) printf("Link: unit test 43 failing\n");
  if(b.find(&k2) != &v20) printf("Link: unit test 44 failing\n");
  if(a.find(&k5) != &v5) printf("Link: unit test 45 failing\n");
  if(b.find(&k5) != &v5) printf("Link: unit test 46 failing\n");
  if(a.find(&k8) != &v8) printf("Link: unit test 47 failing\n");
  if(b.find(&k8) != &v8) printf("Link: unit test 48 failing\n");
  // third delete
  a.del(&k5);
  b.del(&k5);
  if(a.find(&k5) != nullptr) printf("Link: unit test 49 failing\n");
  if(b.find(&k5) != nullptr) printf("Link: unit test 50 failing\n");
  if(a.find(&k1) != &v10) printf("Link: unit test 51 failing\n");
  if(b.find(&k2) != &v20) printf("Link: unit test 52 failing\n");
  if(a.find(&k8) != &v8) printf("Link: unit test 53 failing\n");
  if(b.find(&k8) != &v8) printf("Link: unit test 54 failing\n");
  // fourth delete
  a.del(&k1);
  b.del(&k2);
  if(a.find(&k1) != nullptr) printf("Link: unit test 55 failing\n");
  if(b.find(&k2) != nullptr) printf("Link: unit test 56 failing\n");
  if(a.find(&k8) != &v8) printf("Link: unit test 57 failing\n");
  if(b.find(&k8) != &v8) printf("Link: unit test 58 failing\n");
  // fifth delete
  a.del(&k8);
  b.del(&k8);
  if(a.find(&k8) != nullptr) printf("Link: unit test 59 failing\n");
  if(b.find(&k8) != nullptr) printf("Link: unit test 60 failing\n");
  // sixth delete
  a.del(&k8);
  b.del(&k8);
  if(a.find(&k8) != nullptr) printf("Link: unit test 61 failing\n");
  if(b.find(&k8) != nullptr) printf("Link: unit test 62 failing\n");
  //
  if(!a.isEmpty()) printf("Link: unit test 63 failing\n");
  if(!b.isEmpty()) printf("Link: unit test 64 failing\n");


  // multiple inserts
  #define NUM_KEY 256

  int key[NUM_KEY];
  int val[NUM_KEY];

  for(int i = 0; i < NUM_KEY; ++i){

    key[i]=i;
    val[i] = i*10;

    a.insert(&key[i],&val[i]);

    for(int j = 0; j <= i; ++j){

      if(a.find(&key[j]) != &val[j]) printf("Link: unit test 65 failing\n");

    }

  }

  // multiple delete
  for(int i = 0; i < NUM_KEY; ++i){

    a.del(&key[i]);

    for(int j = 0; j <= i; ++j){

      if(a.find(&key[j]) != nullptr) printf("Link: unit test 66 failing\n");

    }

    for(int j = NUM_KEY - 1; i < j; --j){

      if(a.find(&key[j]) != &val[j]) printf("Link: unit test 67 failing\n");

    }

  }


//  a.print(printKey);
//  printf("\n");


  printf("Link: unit test complete\n");

  return 0;

}
