// link_node.t.c
#include "link_node.h"
#include <stdio.h>
#include <assert.h>
#include <malloc.h>

int LinkNode_test(){

  int errCode = 0;

  fprintf(stderr, "LinkNode: starting unit test\n");

  int val1 = 10;
  int val2 = 20;
  int val3 = 30;

  LinkNode* a = LinkNode_new(1, &val1);
  LinkNode* b = LinkNode_new(2, &val2);
  LinkNode* c = LinkNode_new(3, &val3);

  // checking keys
  if(LinkNode_key(a) != 1){
    fprintf(stderr, "LinkNode: unit test 1.0 failing\n");
    errCode = -1;
  }
  if(LinkNode_key(b) != 2){
    fprintf(stderr, "LinkNode: unit test 1.1 failing\n");
    errCode = -1;
  }
  if(LinkNode_key(c) != 3){
    fprintf(stderr, "LinkNode: unit test 1.2 failing\n");
    errCode = -1;
  }
  // checking values
  if(LinkNode_value(a) != &val1){
    fprintf(stderr, "LinkNode: unit test 2.0 failing\n");
    errCode = -1;
  }
  if(LinkNode_value(b) != &val2){
    fprintf(stderr, "LinkNode: unit test 2.1 failing\n");
    errCode = -1;
  }
  if(LinkNode_value(c) != &val3){
    fprintf(stderr, "LinkNode: unit test 2.2 failing\n");
    errCode = -1;
  }
  // checking next
  if(LinkNode_next(a) != NULL){
    fprintf(stderr, "LinkNode: unit test 3.0 failing\n");
    errCode = -1;
  }
  if(LinkNode_next(b) != NULL){
    fprintf(stderr, "LinkNode: unit test 3.1 failing\n");
    errCode = -1;
  }
  if(LinkNode_next(c) != NULL){
    fprintf(stderr, "LinkNode: unit test 3.2 failing\n");
    errCode = -1;
  }
  // set value
  void* new_value = malloc(sizeof(int));
  LinkNode_setValue(a,new_value);
  if(LinkNode_value(a) != new_value){
    fprintf(stderr,"LinkNode: unit test 4.0 failing\n");
    errCode = -1;
  }
  free(new_value);
  LinkNode_setValue(a,&val1);
  if(LinkNode_value(a) != &val1){
    fprintf(stderr,"LinkNode: unit test 4.1 failing\n");
    errCode = -1;
  }

  // set next
  LinkNode_setNext(a,b);  // takes ownership of b, no need to deallocate 
  LinkNode_setNext(b,c);  // takes owenrship of c, no need to deallocate
  LinkNode_setNext(c,NULL);
  if(LinkNode_next(a) != b){
    fprintf(stderr,"LinkNode: unit test 5.0 failing\n");
    errCode = -1;
  }
  if(LinkNode_next(b) != c){
    fprintf(stderr,"LinkNode: unit test 5.1 failing\n");
    errCode = -1;
  }
  if(LinkNode_next(c) != NULL){
    fprintf(stderr,"LinkNode: unit test 5.2 failing\n");
    errCode = -1;
  }
  // copy
  LinkNode *d = LinkNode_copy(a); // now need to deallocate a and d
  if(d != a){
    fprintf(stderr, "LinkNode: unit test 6.0 failing\n");
    errCode = -1;
  }
  LinkNode *e = LinkNode_copy(c); // need to deallocate e
  if(e != c){
    fprintf(stderr, "LinkNode: unit test 6.1 failing\n");
    errCode = -1;
  }
  LinkNode_setNext(d,e);          // this deallocates b, c. No need to dealloc e 
  if(LinkNode_next(d) != e){
    fprintf(stderr, "LinkNode: unit test 6.2 failing\n");
    errCode = -1;
  }
  if(LinkNode_next(a) != e){
    fprintf(stderr, "LinkNode: unit test 6.3 failing\n");
    errCode = -1;
  }

  LinkNode_delete(d);
  LinkNode_delete(a);

  // checking for memory leaks
  if(LinkNode_hasMemoryLeak()){
    fprintf(stderr, "LinkNode: memory leak detected\n");
    errCode = -1;
  }

  fprintf(stderr, "LinkNode: unit test complete\n");

  return errCode;
}

int main(){
  return LinkNode_test();
}
