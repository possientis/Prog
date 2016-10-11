// link.t.c
#ifndef INCLUDED_LINK
#include "link.h"
#endif

#include <stdio.h>
#include <string>   //std::string


static void printInt(const void* k)
{
  int key = *(int*) k;
  printf("%d",key);
}

static void printString(const void* k)
{
  std::string s = *(std::string*) k;
  printf("%s",s.c_str());

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

static int comp3(const void* x,const void* y)
{
  std::string s = *(std::string*) x;
  std::string t = *(std::string*) y;

  return s.compare(t);

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

  int l1 = 1; // duplicate key
  int l2 = 2; // duplicate key

  int v0 = 0;
  int v1 = 10;
  int v2 = 20;
  int v3 = 30;
  int v5 = 50;
  int v7 = 70;
  int v8 = 80;
  int v10 = 100;
  int v20 = 200;

  std::string c0 = "abc";
  std::string c1 = "def";
  std::string c2 = "ghi";
  std::string c3 = "jkl";
  std::string c4 = "mno";
  std::string c5 = "pqr";
  std::string c6 = "stu";

  std::string d0 = "abc";   // duplicate key

  const char* w0 = "ABC";
  const char* w1 = "DEF";
  const char* w2 = "GHI";
  const char* w3 = "JKL";
  const char* w4 = "MNO";
  const char* w5 = "PQR";
  const char* w6 = "STU";

  const char* w10 = "ABCABC";


  Link a(comp1);
  Link b(comp2);
  Link c(comp3);



  if(!a.isEmpty()) printf("Link: unit test 1 failing\n");
  if(!b.isEmpty()) printf("Link: unit test 2 failing\n");
  if(!c.isEmpty()) printf("Link: unit test 2.0 failing\n");

  // first insert
  a.insert(&k1,&v1);
  b.insert(&k2,&v2);
  c.insert(&c0,&w0);
  if(a.isEmpty()) printf("Link: unit test 3 failing\n");
  if(b.isEmpty()) printf("Link: unit test 4 failing\n");
  if(c.isEmpty()) printf("Link: unit test 4.0 failing\n");
  if(a.find(&k0) != nullptr) printf("Link: unit test 1 failing\n");
  if(a.find(&k1) != &v1) printf("Link: unit test 5 failing\n");
  if(b.find(&k2) != &v2) printf("Link: unit test 6 failing\n");
  if(c.find(&c0) != &w0) printf("Link: unit test 6.0 failing\n");
  // second insert
  a.insert(&k3,&v3);
  b.insert(&k3,&v3);
  c.insert(&c1,&w1);
  if(a.find(&k0) != nullptr) printf("Link: unit test 7 failing\n");
  if(a.find(&k1) != &v1) printf("Link: unit test 8 failing\n");
  if(b.find(&k2) != &v2) printf("Link: unit test 9 failing\n");
  if(c.find(&c0) != &w0) printf("Link: unit test 9.0 failing\n");
  if(a.find(&k3) != &v3) printf("Link: unit test 10 failing\n");
  if(b.find(&k3) != &v3) printf("Link: unit test 11 failing\n");
  if(c.find(&c1) != &w1) printf("Link: unit test 11.0 failing\n");
  // third insert (duplicate keys)
  a.insert(&l1,&v10);   // same key value, yet different address
  b.insert(&l2,&v20);   // same key value, yet different address
  c.insert(&d0,&w10);   // same key value, yet different address
  if(a.find(&k0) != nullptr) printf("Link: unit test 12 failing\n");
  if(a.find(&k1) != &v10) printf("Link: unit test 13 failing\n");
  if(b.find(&k2) != &v20) printf("Link: unit test 14 failing\n");
  if(c.find(&c0) != &w10) printf("Link: unit test 14.0 failing\n");
  if(a.find(&k3) != &v3) printf("Link: unit test 15 failing\n");
  if(b.find(&k3) != &v3) printf("Link: unit test 16 failing\n");
  if(c.find(&c1) != &w1) printf("Link: unit test 16.0 failing\n");
  // fourth insert
  a.insert(&k5,&v5);
  b.insert(&k5,&v5);
  c.insert(&c2,&w2);
  if(a.find(&k0) != nullptr) printf("Link: unit test 17 failing\n");
  if(a.find(&k1) != &v10) printf("Link: unit test 18 failing\n");
  if(b.find(&k2) != &v20) printf("Link: unit test 19 failing\n");
  if(c.find(&c0) != &w10) printf("Link: unit test 19.0 failing\n");
  if(a.find(&k3) != &v3) printf("Link: unit test 20 failing\n");
  if(b.find(&k3) != &v3) printf("Link: unit test 21 failing\n");
  if(c.find(&c1) != &w1) printf("Link: unit test 21.0 failing\n");
  if(a.find(&k5) != &v5) printf("Link: unit test 22 failing\n");
  if(b.find(&k5) != &v5) printf("Link: unit test 23 failing\n");
  if(c.find(&c2) != &w2) printf("Link: unit test 23.0 failing\n");
  // fifth insert
  a.insert(&k8,&v8);
  b.insert(&k8,&v8);
  c.insert(&c3,&w3);
  if(a.find(&k0) != nullptr) printf("Link: unit test 24 failing\n");
  if(a.find(&k1) != &v10) printf("Link: unit test 25 failing\n");
  if(b.find(&k2) != &v20) printf("Link: unit test 26 failing\n");
  if(c.find(&c0) != &w10) printf("Link: unit test 26.0 failing\n");
  if(a.find(&k3) != &v3) printf("Link: unit test 27 failing\n");
  if(b.find(&k3) != &v3) printf("Link: unit test 28 failing\n");
  if(c.find(&c1) != &w1) printf("Link: unit test 28.0 failing\n");
  if(a.find(&k5) != &v5) printf("Link: unit test 29 failing\n");
  if(b.find(&k5) != &v5) printf("Link: unit test 30 failing\n");
  if(c.find(&c2) != &w2) printf("Link: unit test 30.0 failing\n");
  if(a.find(&k8) != &v8) printf("Link: unit test 31 failing\n");
  if(b.find(&k8) != &v8) printf("Link: unit test 32 failing\n");
  if(c.find(&c3) != &w3) printf("Link: unit test 32.0 failing\n");
  // first delete
  a.del(&k3);
  b.del(&k3);
  c.del(&c3);
  if(a.find(&k3) != nullptr) printf("Link: unit test 33 failing\n");
  if(b.find(&k3) != nullptr) printf("Link: unit test 34 failing\n");
  if(c.find(&c3) != nullptr) printf("Link: unit test 34.0 failing\n");
  if(a.find(&k1) != &v10) printf("Link: unit test 35 failing\n");
  if(b.find(&k2) != &v20) printf("Link: unit test 36 failing\n");
  if(c.find(&c0) != &w10) printf("Link: unit test 36.0 failing\n");
  if(a.find(&k5) != &v5) printf("Link: unit test 37 failing\n");
  if(b.find(&k5) != &v5) printf("Link: unit test 38 failing\n");
  if(c.find(&c1) != &w1) printf("Link: unit test 38.0 failing\n");
  if(a.find(&k8) != &v8) printf("Link: unit test 39 failing\n");
  if(b.find(&k8) != &v8) printf("Link: unit test 40 failing\n");
  if(c.find(&c2) != &w2) printf("Link: unit test 40.0 failing\n");
  // second delete (absent key)
  a.del(&k7);
  b.del(&k7);
  c.del(&c5);
  if(a.find(&k0) != nullptr) printf("Link: unit test 41 failing\n");
  if(b.find(&k0) != nullptr) printf("Link: unit test 42 failing\n");
  if(c.find(&c4) != nullptr) printf("Link: unit test 42.0 failing\n");
  if(a.find(&k1) != &v10) printf("Link: unit test 43 failing\n");
  if(b.find(&k2) != &v20) printf("Link: unit test 44 failing\n");
  if(c.find(&c0) != &w10) printf("Link: unit test 44.0 failing\n");
  if(a.find(&k5) != &v5) printf("Link: unit test 45 failing\n");
  if(b.find(&k5) != &v5) printf("Link: unit test 46 failing\n");
  if(c.find(&c1) != &w1) printf("Link: unit test 46.0 failing\n");
  if(a.find(&k8) != &v8) printf("Link: unit test 47 failing\n");
  if(b.find(&k8) != &v8) printf("Link: unit test 48 failing\n");
  if(c.find(&c2) != &w2) printf("Link: unit test 48.0 failing\n");
  // third delete
  a.del(&k5);
  b.del(&k5);
  c.del(&c2);
  if(a.find(&k5) != nullptr) printf("Link: unit test 49 failing\n");
  if(b.find(&k5) != nullptr) printf("Link: unit test 50 failing\n");
  if(c.find(&c2) != nullptr) printf("Link: unit test 50.0 failing\n");
  if(a.find(&k1) != &v10) printf("Link: unit test 51 failing\n");
  if(b.find(&k2) != &v20) printf("Link: unit test 52 failing\n");
  if(c.find(&c0) != &w10) printf("Link: unit test 52.0 failing\n");
  if(a.find(&k8) != &v8) printf("Link: unit test 53 failing\n");
  if(b.find(&k8) != &v8) printf("Link: unit test 54 failing\n");
  if(c.find(&c1) != &w1) printf("Link: unit test 54.0 failing\n");
  // fourth delete
  a.del(&k1);
  b.del(&k2);
  c.del(&c0);
  if(a.find(&k1) != nullptr) printf("Link: unit test 55 failing\n");
  if(b.find(&k2) != nullptr) printf("Link: unit test 56 failing\n");
  if(c.find(&c0) != nullptr) printf("Link: unit test 56.0 failing\n");
  if(a.find(&k8) != &v8) printf("Link: unit test 57 failing\n");
  if(b.find(&k8) != &v8) printf("Link: unit test 58 failing\n");
  if(c.find(&c1) != &w1) printf("Link: unit test 58.0 failing\n");
  // fifth delete
  a.del(&k8);
  b.del(&k8);
  c.del(&c1);
  if(a.find(&k8) != nullptr) printf("Link: unit test 59 failing\n");
  if(b.find(&k8) != nullptr) printf("Link: unit test 60 failing\n");
  if(c.find(&c1) != nullptr) printf("Link: unit test 60.0 failing\n");
  // sixth delete
  a.del(&k8);
  b.del(&k8);
  c.del(&c1);
  if(a.find(&k8) != nullptr) printf("Link: unit test 61 failing\n");
  if(b.find(&k8) != nullptr) printf("Link: unit test 62 failing\n");
  if(c.find(&c1) != nullptr) printf("Link: unit test 62.0 failing\n");
  //
  if(!a.isEmpty()) printf("Link: unit test 63 failing\n");
  if(!b.isEmpty()) printf("Link: unit test 64 failing\n");
  if(!c.isEmpty()) printf("Link: unit test 64.0 failing\n");


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

  // testing iterators
  a.insert(&k1,&v1);
  a.insert(&k3,&v3);
  a.insert(&k5,&v5);
  a.insert(&k7,&v7);

  c.insert(&c1,&w1);
  c.insert(&c2,&w2);
  c.insert(&c3,&w3);
  c.insert(&c4,&w4);


  // first attempt
  for(LinkIter it(a); it; ++it){

    if(a.find(it.key()) != it.val()) printf("Link: unit test 68 failing\n");

  }

  for(LinkIter it(c); it; ++it){

    if(c.find(it.key()) != it.val()) printf("Link: unit test 68.0 failing\n");

  }

  // second attempt
  for(LinkIter it(a); it; ++it){

    if(a.find(it.key()) != it.val()) printf("Link: unit test 69 failing\n");

  }

  for(LinkIter it(c); it; ++it){

    if(c.find(it.key()) != it.val()) printf("Link: unit test 69.0 failing\n");

  }


  bool found[4] = {false,false,false,false};

  for(LinkIter it(a); it; ++it){

    if(it.key() == &k1) found[0] = true;
    else if(it.key() == &k3) found[1] = true;
    else if(it.key() == &k5) found[2] = true;
    else if(it.key() == &k7) found[3] = true;
    else printf("Link: unit test 70 failing\n");

  }

  for(int i = 0; i< 4; ++i){

    if(found[i] == false) printf("Link: unit test 71 failing\n");
    found[i] == false; // needed for next test

  }

  for(LinkIter it(c); it; ++it){

    if(it.key() == &c1) found[0] = true;
    else if(it.key() == &c2) found[1] = true;
    else if(it.key() == &c3) found[2] = true;
    else if(it.key() == &c4) found[3] = true;
    else printf("Link: unit test 71.0 failing\n");

  }

  for(int i = 0; i< 4; ++i){

    if(found[i] == false) printf("Link: unit test 71.1 failing\n");

  }



  //a.print(printInt);
  //printf("\n");
  //c.print(printString);
  //printf("\n");


  printf("Link: unit test complete\n");

  return 0;

}
