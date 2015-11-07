#include <stdio.h>
#include <assert.h>

struct A{
  int data;
  int(*get)(struct A*);
};

int A_get(struct A* pObj){

  assert(pObj != NULL);
  return pObj->data;
}

void A_init(struct A* pObj, int value){

  assert(pObj != NULL);
  pObj->data = value;
  pObj->get = A_get;
}
  

int main(int argc, char* argv[])
{
  struct A a;
  A_init(&a,100);

  printf("a.get() = %d\n",a.get(&a));


  return 0;
}
