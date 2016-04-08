// link.t.c
#include "link.h"
#include <stdio.h>
#include <assert.h>
#include <malloc.h>


int Link_test(){

  int errCode = 0;

  fprintf(stderr, "Link: starting unit test\n");
  // basic new/copy/delete test
  Link *a = Link_new();
  Link *b = Link_copy(a);
  Link_delete(b);
  Link_delete(a);
  if(Link_hasMemoryLeak()){
    fprintf(stderr, "Link: unit test 1.0 failing\n");
    errCode = -1;
  }
  // isEmpty
  a = Link_new();
  b = Link_new();
  if(!Link_isEmpty(a)){
    fprintf(stderr, "Link: unit test 2.0 failing\n");
    errCode = -1;
  }
  if(!Link_isEmpty(b)){
    fprintf(stderr, "Link: unit test 2.1 failing\n");
    errCode = -1;
  }
  // first insert
  int val1 = 10;
  int val2 = 20;
  void* result;
  

  Link_insert(a,1,&val1);
  Link_insert(b,2,&val2);
  if(Link_isEmpty(a)){
    fprintf(stderr, "Link: unit test 3.0 failing\n");
    errCode = -1;
  }
  if(Link_isEmpty(b)){
    fprintf(stderr, "Link: unit test 3.1 failing\n");
    errCode = -1;
  }
  if(Link_find(a, 0, &result)){  // search should fail 
    fprintf(stderr, "Link: unit test 3.2 failing\n");
    errCode = -1;
  }
  if(Link_find(b, 0, &result)){  // search should fail 
    fprintf(stderr, "Link: unit test 3.3 failing\n");
    errCode = -1;
  }
  if(!Link_find(a, 1, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 3.4 failing\n");
    errCode = -1;
  } else {
    if(result != &val1){
      fprintf(stderr, "Link: unit test 3.5 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(b, 2, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 3.6 failing\n");
    errCode = -1;
  } else {
    if(result != &val2){
      fprintf(stderr, "Link: unit test 3.7 failing\n");
      errCode = -1;
    }
  }
  // second insert
  int val3 = 30;
  Link_insert(a, 3, &val3);
  Link_insert(b, 3, &val3);

  if(Link_find(a, 0, &result)){  // search should fail 
    fprintf(stderr, "Link: unit test 4.0 failing\n");
    errCode = -1;
  }
  if(!Link_find(a, 1, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 4.1 failing\n");
    errCode = -1;
  } else {
    if(result != &val1){
      fprintf(stderr, "Link: unit test 4.2 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(b, 2, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 4.3 failing\n");
    errCode = -1;
  } else {
    if(result != &val2){
      fprintf(stderr, "Link: unit test 4.4 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(a, 3, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 4.5 failing\n");
    errCode = -1;
  } else {
    if(result != &val3){
      fprintf(stderr, "Link: unit test 4.6 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(b, 3, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 4.7 failing\n");
    errCode = -1;
  } else {
    if(result != &val3){
      fprintf(stderr, "Link: unit test 4.8 failing\n");
      errCode = -1;
    }
  }
  // third insert duplicate keys
  int newVal1 = 100;
  int newVal2 = 200;

  Link_insert(a, 1, &newVal1);
  Link_insert(b, 2, &newVal2);

  if(Link_find(a, 0, &result)){  // search should fail 
    fprintf(stderr, "Link: unit test 5.0 failing\n");
    errCode = -1;
  }
  if(!Link_find(a, 1, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 5.1 failing\n");
    errCode = -1;
  } else {
    if(result != &newVal1){
      fprintf(stderr, "Link: unit test 5.2 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(b, 2, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 5.3 failing\n");
    errCode = -1;
  } else {
    if(result != &newVal2){
      fprintf(stderr, "Link: unit test 5.4 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(a, 3, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 5.5 failing\n");
    errCode = -1;
  } else {
    if(result != &val3){
      fprintf(stderr, "Link: unit test 5.6 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(b, 3, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 5.7 failing\n");
    errCode = -1;
  } else {
    if(result != &val3){
      fprintf(stderr, "Link: unit test 5.8 failing\n");
      errCode = -1;
    }
  }  

  // fourth insert
  int val5 = 50;
  Link_insert(a, 5, &val5);
  Link_insert(b, 5, &val5);

  if(Link_find(a, 0, &result)){  // search should fail 
    fprintf(stderr, "Link: unit test 6.0 failing\n");
    errCode = -1;
  }
  if(!Link_find(a, 1, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 6.1 failing\n");
    errCode = -1;
  } else {
    if(result != &newVal1){
      fprintf(stderr, "Link: unit test 6.2 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(b, 2, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 6.3 failing\n");
    errCode = -1;
  } else {
    if(result != &newVal2){
      fprintf(stderr, "Link: unit test 6.4 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(a, 3, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 6.5 failing\n");
    errCode = -1;
  } else {
    if(result != &val3){
      fprintf(stderr, "Link: unit test 6.6 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(b, 3, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 6.7 failing\n");
    errCode = -1;
  } else {
    if(result != &val3){
      fprintf(stderr, "Link: unit test 6.8 failing\n");
      errCode = -1;
    }
  }

  if(!Link_find(a, 5, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 6.9 failing\n");
    errCode = -1;
  } else {
    if(result != &val5){
      fprintf(stderr, "Link: unit test 6.10 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(b, 5, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 6.11 failing\n");
    errCode = -1;
  } else {
    if(result != &val5){
      fprintf(stderr, "Link: unit test 6.12 failing\n");
      errCode = -1;
    }
  }

  // fifth insert
  int val8 = 80;
  Link_insert(a, 8, &val8);
  Link_insert(b, 8, &val8);

  if(Link_find(a, 0, &result)){  // search should fail 
    fprintf(stderr, "Link: unit test 7.0 failing\n");
    errCode = -1;
  }
  if(!Link_find(a, 1, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 7.1 failing\n");
    errCode = -1;
  } else {
    if(result != &newVal1){
      fprintf(stderr, "Link: unit test 7.2 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(b, 2, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 7.3 failing\n");
    errCode = -1;
  } else {
    if(result != &newVal2){
      fprintf(stderr, "Link: unit test 7.4 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(a, 3, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 7.5 failing\n");
    errCode = -1;
  } else {
    if(result != &val3){
      fprintf(stderr, "Link: unit test 7.6 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(b, 3, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 7.7 failing\n");
    errCode = -1;
  } else {
    if(result != &val3){
      fprintf(stderr, "Link: unit test 7.8 failing\n");
      errCode = -1;
    }
  }

  if(!Link_find(a, 5, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 7.9 failing\n");
    errCode = -1;
  } else {
    if(result != &val5){
      fprintf(stderr, "Link: unit test 7.10 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(b, 5, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 7.11 failing\n");
    errCode = -1;
  } else {
    if(result != &val5){
      fprintf(stderr, "Link: unit test 7.12 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(a, 8, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 7.13 failing\n");
    errCode = -1;
  } else {
    if(result != &val8){
      fprintf(stderr, "Link: unit test 7.14 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(b, 8, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 7.15 failing\n");
    errCode = -1;
  } else {
    if(result != &val8){
      fprintf(stderr, "Link: unit test 7.16 failing\n");
      errCode = -1;
    }
  }
  // first remove
  Link_remove(a,3);
  Link_remove(b,3);
  
  if(Link_find(a, 3, &result)){  // search should fail 
    fprintf(stderr, "Link: unit test 8.0.1 failing\n");
    errCode = -1;
  }
  if(Link_find(b, 3, &result)){  // search should fail 
    fprintf(stderr, "Link: unit test 8.0.2 failing\n");
    errCode = -1;
  }
  if(!Link_find(a, 1, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 8.1 failing\n");
    errCode = -1;
  } else {
    if(result != &newVal1){
      fprintf(stderr, "Link: unit test 8.2 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(b, 2, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 8.3 failing\n");
    errCode = -1;
  } else {
    if(result != &newVal2){
      fprintf(stderr, "Link: unit test 8.4 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(a, 5, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 8.9 failing\n");
    errCode = -1;
  } else {
    if(result != &val5){
      fprintf(stderr, "Link: unit test 8.10 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(b, 5, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 8.11 failing\n");
    errCode = -1;
  } else {
    if(result != &val5){
      fprintf(stderr, "Link: unit test 8.12 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(a, 8, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 8.13 failing\n");
    errCode = -1;
  } else {
    if(result != &val8){
      fprintf(stderr, "Link: unit test 8.14 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(b, 8, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 8.15 failing\n");
    errCode = -1;
  } else {
    if(result != &val8){
      fprintf(stderr, "Link: unit test 8.16 failing\n");
      errCode = -1;
    }
  }

  // second remove. Removing absent key.
  Link_remove(a,7);
  Link_remove(b,7);

  if(Link_find(a, 0, &result)){  // search should fail 
    fprintf(stderr, "Link: unit test 9.0 failing\n");
    errCode = -1;
  }
  if(Link_find(b, 0, &result)){  // search should fail 
    fprintf(stderr, "Link: unit test 9.1 failing\n");
    errCode = -1;
  }
  if(!Link_find(a, 1, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 9.2 failing\n");
    errCode = -1;
  } else {
    if(result != &newVal1){
      fprintf(stderr, "Link: unit test 9.3 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(b, 2, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 9.4 failing\n");
    errCode = -1;
  } else {
    if(result != &newVal2){
      fprintf(stderr, "Link: unit test 9.5 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(a, 5, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 9.6 failing\n");
    errCode = -1;
  } else {
    if(result != &val5){
      fprintf(stderr, "Link: unit test 9.7 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(b, 5, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 9.11 failing\n");
    errCode = -1;
  } else {
    if(result != &val5){
      fprintf(stderr, "Link: unit test 9.12 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(a, 8, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 9.13 failing\n");
    errCode = -1;
  } else {
    if(result != &val8){
      fprintf(stderr, "Link: unit test 9.14 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(b, 8, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 9.15 failing\n");
    errCode = -1;
  } else {
    if(result != &val8){
      fprintf(stderr, "Link: unit test 9.16 failing\n");
      errCode = -1;
    }
  }
  // third remove. 
  Link_remove(a,5);
  Link_remove(b,5);

  if(Link_find(a, 5, &result)){  // search should fail 
    fprintf(stderr, "Link: unit test 10.0 failing\n");
    errCode = -1;
  }
  if(Link_find(b, 5, &result)){  // search should fail 
    fprintf(stderr, "Link: unit test 10.1 failing\n");
    errCode = -1;
  }
  if(!Link_find(a, 1, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 10.2 failing\n");
    errCode = -1;
  } else {
    if(result != &newVal1){
      fprintf(stderr, "Link: unit test 10.3 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(b, 2, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 10.4 failing\n");
    errCode = -1;
  } else {
    if(result != &newVal2){
      fprintf(stderr, "Link: unit test 10.5 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(a, 8, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 10.6 failing\n");
    errCode = -1;
  } else {
    if(result != &val8){
      fprintf(stderr, "Link: unit test 10.7 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(b, 8, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 10.8 failing\n");
    errCode = -1;
  } else {
    if(result != &val8){
      fprintf(stderr, "Link: unit test 10.9 failing\n");
      errCode = -1;
    }
  }
  // fourth remove. 
  Link_remove(a,1);
  Link_remove(b,2);

  if(Link_find(a, 1, &result)){  // search should fail 
    fprintf(stderr, "Link: unit test 11.0 failing\n");
    errCode = -1;
  }
  if(Link_find(b, 2, &result)){  // search should fail 
    fprintf(stderr, "Link: unit test 11.1 failing\n");
    errCode = -1;
  }
 if(!Link_find(a, 8, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 11.2 failing\n");
    errCode = -1;
  } else {
    if(result != &val8){
      fprintf(stderr, "Link: unit test 11.3 failing\n");
      errCode = -1;
    }
  }
  if(!Link_find(b, 8, &result)){  // search should succeed 
    fprintf(stderr, "Link: unit test 11.4 failing\n");
    errCode = -1;
  } else {
    if(result != &val8){
      fprintf(stderr, "Link: unit test 11.4 failing\n");
      errCode = -1;
    }
  }
  // fifth remove. 
  Link_remove(a,8);
  Link_remove(b,8);

  if(Link_find(a, 8, &result)){  // search should fail 
    fprintf(stderr, "Link: unit test 12.0 failing\n");
    errCode = -1;
  }
  if(Link_find(b, 8, &result)){  // search should fail 
    fprintf(stderr, "Link: unit test 12.1 failing\n");
    errCode = -1;
  }
  if(!Link_isEmpty(a)){
    fprintf(stderr, "Link: unit test 12.2 failing\n");
    errCode = -1;
  }
  if(!Link_isEmpty(b)){
    fprintf(stderr, "Link: unit test 12.3 failing\n");
    errCode = -1;
  }
  // sixth remove. same 
  Link_remove(a,8);
  Link_remove(b,8);

  if(Link_find(a, 8, &result)){  // search should fail 
    fprintf(stderr, "Link: unit test 13.0 failing\n");
    errCode = -1;
  }
  if(Link_find(b, 8, &result)){  // search should fail 
    fprintf(stderr, "Link: unit test 13.1 failing\n");
    errCode = -1;
  }
  if(!Link_isEmpty(a)){
    fprintf(stderr, "Link: unit test 13.2 failing\n");
    errCode = -1;
  }
  if(!Link_isEmpty(b)){
    fprintf(stderr, "Link: unit test 13.3 failing\n");
    errCode = -1;
  }
  
#define LINK_T_C_NUM_SIMUL 512
  void* values[LINK_T_C_NUM_SIMUL];
  int i;
  // multiple insert
  for(i = 0; i < LINK_T_C_NUM_SIMUL; ++i){
    values[i] = &values[i];  // giving void* pointer some unique value
    Link_insert(a, i, values[i]);
  }
  for(i = 0; i < LINK_T_C_NUM_SIMUL; ++i){
    if(!Link_find(a, i, &result)){  // search should succeed 
      fprintf(stderr, "Link: unit test 14.0 failing for i = %d\n", i);
      errCode = -1;
    } else {
      if(result != values[i]){
        fprintf(stderr, "Link: unit test 14.1 failing for i = %d\n", i);
        errCode = -1;
      }
    }
  }
  // multiple remove
  for(i = 0; i < LINK_T_C_NUM_SIMUL; ++i){
    Link_remove(a, i);
  }
  for(i = 0; i < LINK_T_C_NUM_SIMUL; ++i){
    if(Link_find(a, i, &result)){  // search should fail
      fprintf(stderr, "Link: unit test 14.2 failing for i = %d\n", i);
      errCode = -1;
    }
  }
  if(!Link_isEmpty(a)){
    fprintf(stderr, "Link: unit test 14.3 failing\n");
    errCode = -1;
  }
  // testing iterators
  // basic new/copy/delete test
  LinkIter* iter1 = LinkIter_new(a);
  LinkIter* iter2 = LinkIter_copy(iter1);
  LinkIter_delete(iter1);
  LinkIter_delete(iter2);
  Link_delete(a); // so memory leak test succeeds
  Link_delete(b); // so memory leak test succeeds
  if(Link_hasMemoryLeak()){
    fprintf(stderr, "Link: unit test 15.0 failing\n");
    errCode = -1;
  }
  if(LinkNode_hasMemoryLeak()){
    fprintf(stderr, "Link: unit test 15.1 failing\n");
    errCode = -1;
  }

  //
  a = Link_new();
  Link_insert(a, 1, &val1);
  Link_insert(a, 3, &val3);
  Link_insert(a, 5, &val5);
  Link_insert(a, 8, &val8);

  LinkIter *iter = LinkIter_new(a);
  while(LinkIter_hasNext(iter)){
    LinkIter_moveNext(iter);
    int key     = LinkIter_key(iter);
    void* value = LinkIter_value(iter);
    if(!Link_find(a, key, &result)){  // search should succeed 
      fprintf(stderr, "Link: unit test 16.0 failing for key = %d\n", key);
      errCode = -1;
    } else {
      if(result != value){
        fprintf(stderr, "Link: unit test 16.1 failing for key = %d\n", key);
        errCode = -1;
      }
    }
  }
 
  LinkIter_delete(iter);
  Link_delete(a);
  // final check for memory leaks
  if(Link_hasMemoryLeak()){
    fprintf(stderr, "Link: memory leak detected\n");
    errCode = -1;
  }
  if(LinkNode_hasMemoryLeak()){
    fprintf(stderr, "Link: memory leak detected for nodes\n");
    errCode = -1;
  }


  fprintf(stderr, "Link: unit test complete\n");
  return errCode;
}

int main(){
  return Link_test();
}


