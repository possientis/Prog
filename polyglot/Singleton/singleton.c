// Singleton design pattern
#include <stdio.h>
#include <assert.h>
#include <malloc.h>

typedef struct SingleObject_ {
  // instance methods
  void (*showMessage)();
  // instance data
} SingleObject;


// implementing function pointer member
void SingleObject_showMessage(){
  printf("The single object is alive and well\n");
}

// initializer of struct
void SingleObject_init(SingleObject* pObj /* , no other data */){
  assert(pObj != NULL);
  pObj->showMessage = SingleObject_showMessage;
}

// new pointer to initialized struct
SingleObject* SingleObject_new(){
  static int mBuilt = 0;
  if(mBuilt == 1){
    fprintf(stderr,"SingleObject: cannot create new instance\n");
    return NULL;
  }
  mBuilt =1;
  SingleObject *pObj = (SingleObject*) malloc(sizeof(SingleObject));
  SingleObject_init(pObj);
  return pObj;
}

// delete pointer to struct
void SingleObject_free(SingleObject* pObj){
  free(pObj); 
}

SingleObject *SingleObject_getInstance(){
  static SingleObject* mInstance = NULL;
  if(mInstance == NULL){
    mInstance = SingleObject_new();
  }
  return mInstance;
}


int main(int argc, char* argv[]){

  SingleObject* object1 = SingleObject_getInstance();
  assert(object1 != NULL);
  object1->showMessage();


  SingleObject* object2 = SingleObject_getInstance();
  if(object1 == object2){
    printf("The two objects are the same\n");
  }
  
  // the below line fails:
  //SingleObject* object3 = SingleObject_new();
  // However, the below will succeed:
  // SingleObject object4;
  // SingleObject_init(&object4);

  SingleObject_free(object1);
  return 0;
}
