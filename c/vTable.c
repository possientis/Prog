#include <stdio.h>
#include <assert.h>
#include <malloc.h>

// needed to implement class A
struct A_vTable;

// class A implemented as data + pointer to vTable
typedef struct A_{
  int data;
  struct A_vTable* ops;
} A;

// vTable has list of pointers to methods of A
// There is no 'this' pointer in C. Each method
// signature contains an A* argument, equivalent
// to the 'self' argument (first argument) in python
struct A_vTable{
  int(*get)(A*);
};

// actual implementation of methods are needed
// to initialize vTable with the appropriate 
// function pointers.
int A_get(A* pObj){
  assert(pObj != NULL);
  return pObj->data;
}

// implementation of vTable
void A_vTable_init(struct A_vTable* pObj){
  assert(pObj != NULL);
  pObj->get = A_get;
}

// A_vTable is a singleton
struct A_vTable* A_vTable_get(){
  static struct A_vTable* pObj = NULL;
  if(pObj == NULL){
    pObj = (struct A_vTable*) malloc(sizeof(struct A_vTable));
    assert(pObj != NULL);
    A_vTable_init(pObj);
  }
  return pObj;
}

void A_vTable_free(){
  struct A_vTable* pObj = A_vTable_get();
  free(pObj);
}

// implementation of class A
void A_init(A* pObj, int value){
  assert(pObj != NULL);
  pObj->data = value;
  pObj->ops = A_vTable_get();
}

// allocating a new object from the heap
A* A_new(int value){
  A* pObj = (A*) malloc(sizeof(A));
  assert(pObj != NULL);
  A_init(pObj,value);
  return pObj;
}

// simple implementation without
// reference counting on vTable
// which needs to be freed separately
void A_free(A* pObj){
  free(pObj);
}

int main(int argc, char* argv[])
{
  A a;
  A b;
  A c;
  A* d = A_new(400);
  A* e = A_new(500);

  A_init(&a,100);
  A_init(&b,200);
  A_init(&c,300);
  printf("a.get() = %d\n",a.ops->get(&a));
  printf("b.get() = %d\n",b.ops->get(&b));
  printf("c.get() = %d\n",c.ops->get(&c));
  printf("d.get() = %d\n",d->ops->get(d));
  printf("e.get() = %d\n",e->ops->get(e));

  // clean up
  A_free(d);
  A_free(e);
  A_vTable_free();

  return 0;
}
