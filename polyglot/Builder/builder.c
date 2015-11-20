// Builder Design Pattern
#define MAX_MEAL_ITEMS 5  // maximum number of items per meal object
#include <assert.h>
#include <malloc.h>
#include <stdio.h>
// The main idea behind the builder design pattern is
// to provide an abstract interface for a 'builder object'
// A concrete builder object is not a factory object which returns
// a ready-made object of a certain type. A concrete builder object
// should be viewed as a toolbox allowing someone else (that someone
// else is called 'a director' within the context of the builer design
// pattern) to build an object of some type according to some plan.

// Let us define a possible 'director' class, whose purpose
// it is to manufacture meals

////////////////////////////////////////////////////////////////////////////////
//                           Packing                                          //
////////////////////////////////////////////////////////////////////////////////

typedef struct Packing_ Packing;
struct Packing_ {
  void* object;                             // pointer to concrete object
  const char* (*pack)(/* Packing* */);      // virtual method and no 'this' pointer
  void (*delete)(Packing*);                 // virtual delete operator
};

void Packing_init(Packing* pObj, void* object, 
    const char* (*pack)(), void (*delete)(Packing*)){
  assert(pObj != NULL);
  pObj->object = object;
  pObj->pack = pack;
  pObj->delete = delete;
}

void Packing_destroy(Packing* pObj){
  assert(pObj != NULL);
  pObj->object = NULL;
  pObj->pack = NULL;
  pObj->delete = NULL;
}

// virtual
void Packing_delete(Packing* pObj){
  assert(pObj != NULL);
  void (*delete)(Packing*);
  delete = pObj->delete;  // retrieve function pointer to delete function
  delete(pObj);           // deletes pointer to concrete object
}


////////////////////////////////////////////////////////////////////////////////
//                           Wrapper                                          //
////////////////////////////////////////////////////////////////////////////////

typedef struct Wrapper_ Wrapper;
struct Wrapper_ {
  Packing base;
};

const char* Wrapper_pack(){
  return "Wrapper";
}

void Wrapper_destroy(Wrapper* pObj){
  assert(pObj != NULL);
  Packing_destroy(&pObj->base);
}

// override
void Wrapper_delete(Packing* pObj){
  assert(pObj != NULL);
  Wrapper* object = (Wrapper*) pObj->object;  // pointer to concrete object
  Wrapper_destroy(object);                    // clears memory area
  free(object);                               // frees concrete pointer
}

void Wrapper_init(Wrapper* pObj){
  assert(pObj != NULL);
  Packing_init(&pObj->base, (void*) pObj, Wrapper_pack, Wrapper_delete);
}

Wrapper* Wrapper_new(){
  Wrapper* pObj = (Wrapper*) malloc(sizeof(Wrapper));
  Wrapper_init(pObj);
  return pObj;
}

void Wrapper_test(){
  // stack
  printf("Creating wrapper object from the stack: ");
  Wrapper w;
  Wrapper_init(&w);
  printf("pack: %s\n",w.base.pack());
  Wrapper_destroy(&w);
  //heap
  printf("Creating wrapper object from the heap: ");
  Wrapper* p = Wrapper_new();
  printf("pack: %s\n",p->base.pack());
  Packing_delete(&p->base); // should call Wrapper_delete
}

////////////////////////////////////////////////////////////////////////////////
//                           Bottle                                          //
////////////////////////////////////////////////////////////////////////////////

typedef struct Bottle_ Bottle;
struct Bottle_ {
  Packing base;
};

const char* Bottle_pack(){
  return "Bottle";
}

void Bottle_destroy(Bottle* pObj){
  assert(pObj != NULL);
  Packing_destroy(&pObj->base);
}

// override
void Bottle_delete(Packing* pObj){
  assert(pObj != NULL);
  Bottle* object = (Bottle*) pObj->object;
  Bottle_destroy(object);
  free (object);
}

void Bottle_init(Bottle* pObj){
  assert(pObj != NULL);
  Packing_init(&pObj->base, (void*) pObj, Bottle_pack, Bottle_delete);
}

Bottle* Bottle_new(){
  Bottle* pObj = (Bottle*) malloc(sizeof(Bottle));
  Bottle_init(pObj);
  return pObj;
}

void Bottle_test(){
  // stack
  printf("Creating bottle object from the stack: ");
  Bottle w;
  Bottle_init(&w);
  printf("pack: %s\n",w.base.pack());
  Bottle_destroy(&w);
  // heap
  printf("Creating bottle object from the heap: ");
  Bottle* p = Bottle_new();
  printf("pack %s\n",p->base.pack());
  Packing_delete(&p->base);   // should call Bottle_delete(Packing*)
}

////////////////////////////////////////////////////////////////////////////////
//                             ItemOps                                        //
////////////////////////////////////////////////////////////////////////////////

typedef struct Item_ Item;

typedef struct ItemOps_ ItemOps;
struct ItemOps_ {
  int count;                                // reference count
  double (*price)();                 
  const char* (*name)();            
  Packing* (*packing)();               
  void (*delete)(Item*);                    // virtual destructor
};

void ItemOps_init(ItemOps* pObj, double (*price)(), 
    const char* (*name)(), Packing* (*packing)(),
    void (*delete)(Item*)){
  assert(pObj != NULL);
  pObj->count = 0;
  pObj->price = price;
  pObj->name = name;
  pObj->packing = packing;
  pObj->delete = delete;
}

void ItemOps_destroy(ItemOps* pObj){
  assert(pObj != NULL);
  pObj->count = 0;
  pObj->price = NULL;
  pObj->name = NULL;
  pObj->packing = NULL;
  pObj->delete = NULL;
}

ItemOps* ItemOps_new(double (*price)(), const char* (*name)(),
    Packing* (*packing)(), void (*delete)(Item*)){
  ItemOps* pObj = (ItemOps*) malloc(sizeof(ItemOps));
  ItemOps_init(pObj,price,name,packing,delete);
  return pObj;
}

void ItemOps_delete(ItemOps* pObj){
  assert(pObj != NULL);
  ItemOps_destroy(pObj);
  free(pObj);
}

////////////////////////////////////////////////////////////////////////////////
//                                   Item                                     //
////////////////////////////////////////////////////////////////////////////////

struct Item_ {
  void* object;                             // pointer to concrete object
  ItemOps* ops;
};

void Item_init(Item* pObj, void* object, ItemOps* ops){
  assert(pObj != NULL);
  pObj->object = object;
  pObj->ops = ops;
}

void Item_destroy(Item* pObj){
  assert(pObj != NULL);
  pObj->object = NULL;        
  pObj->ops = NULL;           
};

void Item_delete(Item* pObj){
  assert(pObj != NULL);
  void (*delete)(Item*);
  delete = pObj->ops->delete;
  delete(pObj);
}

////////////////////////////////////////////////////////////////////////////////
//                               Burger                                       //
////////////////////////////////////////////////////////////////////////////////

typedef struct Burger_ Burger;
struct Burger_ {
  Item base;
};

Packing* Burger_packing(){
  return &Wrapper_new()->base;
}

void Burger_init(Burger* pObj, void* object, ItemOps* ops){
  assert(pObj != NULL);
  assert(ops != NULL);
  assert(ops->packing == Burger_packing);
  Item_init(&pObj->base,object,ops);
}

void Burger_destroy(Burger* pObj){
  assert(pObj != NULL);
  Item_destroy(&pObj->base);
}

////////////////////////////////////////////////////////////////////////////////
//                             ColdDrink                                      //
////////////////////////////////////////////////////////////////////////////////

typedef struct ColdDrink_ ColdDrink;
struct ColdDrink_ {
  Item base;
};

Packing* ColdDrink_packing(){
  return &Bottle_new()->base;
}

void ColdDrink_init(ColdDrink* pObj, void* object, ItemOps* ops){
  assert(pObj != NULL);
  assert(ops != NULL);
  assert(ops->packing == ColdDrink_packing);
  Item_init(&pObj->base,object,ops);
}

void ColdDrink_destroy(ColdDrink* pObj){
  assert(pObj != NULL);
  Item_destroy(&pObj->base);
}


////////////////////////////////////////////////////////////////////////////////
//                             VegBurger                                      //
////////////////////////////////////////////////////////////////////////////////

typedef struct VegBurger_ VegBurger;
struct VegBurger_ {
  Burger base;
};

ItemOps* VegBurger_opsHandle(int);                // forward declaration
void VegBurger_destroy(VegBurger* pObj){
  assert(pObj != NULL);
  Burger_destroy(&pObj->base);
  VegBurger_opsHandle(1);   // decrementing reference counter to ItemOps object
}

double VegBurger_price(){return 2.5;}
const char* VegBurger_name(){return "Veg Burger";}

void VegBurger_delete(Item* pObj){
  assert(pObj != NULL);
  VegBurger* object = (VegBurger*) pObj->object;
  VegBurger_destroy(object);
  free(object);
}

ItemOps* VegBurger_opsHandle(int freeHandle){ 
  // set freeHandle = 1 to free handle, else 0
  // attempting to emulate the singleton pattern
  // there should be at most one ItemOps object across all VegBurger instances
  // This object is maintained via a static pointer in function scope
  // This function is used both to obtain and to release handle

  // unique ItemsOps object across all VegBurger instances
  static ItemOps* ops = NULL;
  
  // freeHandle = 1 to free handle, freeHandle = 0 to obtain handle
  assert(freeHandle == 1 || freeHandle == 0);

  if(freeHandle == 0){      // getting handle
    if(ops == NULL){        // object not yet instantiated
      ops = (ItemOps*) malloc(sizeof(ItemOps));
      ItemOps_init(ops,VegBurger_price,VegBurger_name,Burger_packing,
          VegBurger_delete);
    }
    ops->count++;           // one more handle pointing ItemOps object
    return ops;
  }
  else{                     //freeing handle
    assert(freeHandle == 1);
    assert(ops != NULL);
    assert(ops->count > 0);
    ops->count--;           // one less handle pointing to ItemOps object
    if(ops->count == 0){
      ItemOps_destroy(ops);
      free(ops);
      ops = NULL;
    }
    return NULL;
  }
}

void VegBurger_init(VegBurger* pObj){
  assert(pObj != NULL);
  ItemOps* ops =  VegBurger_opsHandle(0);
  Burger_init(&pObj->base, (void*) pObj, ops);
}

VegBurger* VegBurger_new(){
  VegBurger* pObj = (VegBurger*) malloc(sizeof(VegBurger));
  VegBurger_init(pObj);
  return pObj;
}

void VegBurger_test(){

  // stack
  printf("Creating VegBurger object from the stack ...\n");
  VegBurger v;
  VegBurger_init(&v);
  printf("name: %s\n", v.base.base.ops->name());
  printf("price: %f\n", v.base.base.ops->price());
  Packing* pack1 = v.base.base.ops->packing();
  printf("packing: %s\n", pack1->pack());
  Packing_delete(pack1);
  VegBurger_destroy(&v);
  // heap
  printf("Creating VegBurger object from the heap ...\n");
  VegBurger* p = VegBurger_new();
  printf("name: %s\n", p->base.base.ops->name());
  printf("price: %f\n", p->base.base.ops->price());
  Packing* pack2 = p->base.base.ops->packing();
  printf("packing: %s\n", pack2->pack());
  Packing_delete(pack2);
  Item_delete(&p->base.base);   // should call VegBurger_delete(Item*)
}

////////////////////////////////////////////////////////////////////////////////
//                             ChickenBurger                                  //
////////////////////////////////////////////////////////////////////////////////

typedef struct ChickenBurger_ ChickenBurger;
struct ChickenBurger_ {
  Burger base;
};

ItemOps* ChickenBurger_opsHandle(int);                // forward declaration
void ChickenBurger_destroy(ChickenBurger* pObj){
  assert(pObj != NULL);
  Burger_destroy(&pObj->base);
  ChickenBurger_opsHandle(1);   // decrementing reference counter to ItemOps object
}

double ChickenBurger_price(){return 5.05;}
const char* ChickenBurger_name(){return "Chicken Burger";}

void ChickenBurger_delete(Item* pObj){
  assert(pObj != NULL);
  ChickenBurger* object = (ChickenBurger*) pObj->object;
  ChickenBurger_destroy(object);
  free(object);
}

ItemOps* ChickenBurger_opsHandle(int freeHandle){ 
  // set freeHandle = 1 to free handle, else 0
  // attempting to emulate the singleton pattern
  // there should be at most one ItemOps object across all ChickenBurger instances
  // This object is maintained via a static pointer in function scope
  // This function is used both to obtain and to release handle

  // unique ItemsOps object across all ChickenBurger instances
  static ItemOps* ops = NULL;
  
  // freeHandle = 1 to free handle, freeHandle = 0 to obtain handle
  assert(freeHandle == 1 || freeHandle == 0);

  if(freeHandle == 0){      // getting handle
    if(ops == NULL){        // object not yet instantiated
      ops = (ItemOps*) malloc(sizeof(ItemOps));
      ItemOps_init(ops,ChickenBurger_price,ChickenBurger_name,Burger_packing,
          ChickenBurger_delete);
    }
    ops->count++;           // one more handle pointing ItemOps object
    return ops;
  }
  else{                     //freeing handle
    assert(freeHandle == 1);
    assert(ops != NULL);
    assert(ops->count > 0);
    ops->count--;           // one less handle pointing to ItemOps object
    if(ops->count == 0){
      ItemOps_destroy(ops);
      free(ops);
      ops = NULL;
    }
    return NULL;
  }
}

void ChickenBurger_init(ChickenBurger* pObj){
  assert(pObj != NULL);
  ItemOps* ops =  ChickenBurger_opsHandle(0);
  Burger_init(&pObj->base, (void*) pObj, ops);
}

ChickenBurger* ChickenBurger_new(){
  ChickenBurger* pObj = (ChickenBurger*) malloc(sizeof(ChickenBurger));
  ChickenBurger_init(pObj);
  return pObj;
}

void ChickenBurger_test(){

  // stack
  printf("Creating ChickenBurger object from the stack ...\n");
  ChickenBurger v;
  ChickenBurger_init(&v);
  printf("name: %s\n", v.base.base.ops->name());
  printf("price: %f\n", v.base.base.ops->price());
  Packing* pack1 = v.base.base.ops->packing();
  printf("packing: %s\n", pack1->pack());
  Packing_delete(pack1);
  ChickenBurger_destroy(&v);
  // heap
  printf("Creating ChickenBurger object from the heap ...\n");
  ChickenBurger* p = ChickenBurger_new();
  printf("name: %s\n", p->base.base.ops->name());
  printf("price: %f\n", p->base.base.ops->price());
  Packing* pack2 = p->base.base.ops->packing();
  printf("packing: %s\n", pack2->pack());
  Packing_delete(pack2);
  Item_delete(&p->base.base);   // should call ChickenBurger_delete(Item*)
}


////////////////////////////////////////////////////////////////////////////////
//                                Coke                                        //
////////////////////////////////////////////////////////////////////////////////

typedef struct Coke_ Coke;
struct Coke_ {
  ColdDrink base;
};

ItemOps* Coke_opsHandle(int);                // forward declaration
void Coke_destroy(Coke* pObj){
  assert(pObj != NULL);
  ColdDrink_destroy(&pObj->base);
  Coke_opsHandle(1);   // decrementing reference counter to ItemOps object
}

double Coke_price(){return 3.0;}
const char* Coke_name(){return "Coke";}

void Coke_delete(Item* pObj){
  assert(pObj != NULL);
  Coke* object = (Coke*) pObj->object;
  Coke_destroy(object);
  free(object);
}

ItemOps* Coke_opsHandle(int freeHandle){ 
  // set freeHandle = 1 to free handle, else 0
  // attempting to emulate the singleton pattern
  // there should be at most one ItemOps object across all Coke instances
  // This object is maintained via a static pointer in function scope
  // This function is used both to obtain and to release handle

  // unique ItemsOps object across all Coke instances
  static ItemOps* ops = NULL;
  
  // freeHandle = 1 to free handle, freeHandle = 0 to obtain handle
  assert(freeHandle == 1 || freeHandle == 0);

  if(freeHandle == 0){      // getting handle
    if(ops == NULL){        // object not yet instantiated
      ops = (ItemOps*) malloc(sizeof(ItemOps));
      ItemOps_init(ops,Coke_price,Coke_name,ColdDrink_packing,
          Coke_delete);
    }
    ops->count++;           // one more handle pointing ItemOps object
    return ops;
  }
  else{                     //freeing handle
    assert(freeHandle == 1);
    assert(ops != NULL);
    assert(ops->count > 0);
    ops->count--;           // one less handle pointing to ItemOps object
    if(ops->count == 0){
      ItemOps_destroy(ops);
      free(ops);
      ops = NULL;
    }
    return NULL;
  }
}

void Coke_init(Coke* pObj){
  assert(pObj != NULL);
  ItemOps* ops =  Coke_opsHandle(0);
  ColdDrink_init(&pObj->base, (void*) pObj, ops);
}

Coke* Coke_new(){
  Coke* pObj = (Coke*) malloc(sizeof(Coke));
  Coke_init(pObj);
  return pObj;
}

void Coke_test(){

  // stack
  printf("Creating Coke object from the stack ...\n");
  Coke v;
  Coke_init(&v);
  printf("name: %s\n", v.base.base.ops->name());
  printf("price: %f\n", v.base.base.ops->price());
  Packing* pack1 = v.base.base.ops->packing();
  printf("packing: %s\n", pack1->pack());
  Packing_delete(pack1);
  Coke_destroy(&v);
  // heap
  printf("Creating Coke object from the heap ...\n");
  Coke* p = Coke_new();
  printf("name: %s\n", p->base.base.ops->name());
  printf("price: %f\n", p->base.base.ops->price());
  Packing* pack2 = p->base.base.ops->packing();
  printf("packing: %s\n", pack2->pack());
  Packing_delete(pack2);
  Item_delete(&p->base.base);   // should call Coke_delete(Item*)
}


////////////////////////////////////////////////////////////////////////////////
//                                Pepsi                                       //
////////////////////////////////////////////////////////////////////////////////

typedef struct Pepsi_ Pepsi;
struct Pepsi_ {
  ColdDrink base;
};

ItemOps* Pepsi_opsHandle(int);                // forward declaration
void Pepsi_destroy(Pepsi* pObj){
  assert(pObj != NULL);
  ColdDrink_destroy(&pObj->base);
  Pepsi_opsHandle(1);   // decrementing reference counter to ItemOps object
}

double Pepsi_price(){return 3.5;}
const char* Pepsi_name(){return "Pepsi";}

void Pepsi_delete(Item* pObj){
  assert(pObj != NULL);
  Pepsi* object = (Pepsi*) pObj->object;
  Pepsi_destroy(object);
  free(object);
}

ItemOps* Pepsi_opsHandle(int freeHandle){ 
  // set freeHandle = 1 to free handle, else 0
  // attempting to emulate the singleton pattern
  // there should be at most one ItemOps object across all Pepsi instances
  // This object is maintained via a static pointer in function scope
  // This function is used both to obtain and to release handle

  // unique ItemsOps object across all Pepsi instances
  static ItemOps* ops = NULL;
  
  // freeHandle = 1 to free handle, freeHandle = 0 to obtain handle
  assert(freeHandle == 1 || freeHandle == 0);

  if(freeHandle == 0){      // getting handle
    if(ops == NULL){        // object not yet instantiated
      ops = (ItemOps*) malloc(sizeof(ItemOps));
      ItemOps_init(ops,Pepsi_price,Pepsi_name,ColdDrink_packing,
          Pepsi_delete);
    }
    ops->count++;           // one more handle pointing ItemOps object
    return ops;
  }
  else{                     //freeing handle
    assert(freeHandle == 1);
    assert(ops != NULL);
    assert(ops->count > 0);
    ops->count--;           // one less handle pointing to ItemOps object
    if(ops->count == 0){
      ItemOps_destroy(ops);
      free(ops);
      ops = NULL;
    }
    return NULL;
  }
}

void Pepsi_init(Pepsi* pObj){
  assert(pObj != NULL);
  ItemOps* ops =  Pepsi_opsHandle(0);
  ColdDrink_init(&pObj->base, (void*) pObj, ops);
}

Pepsi* Pepsi_new(){
  Pepsi* pObj = (Pepsi*) malloc(sizeof(Pepsi));
  Pepsi_init(pObj);
  return pObj;
}

void Pepsi_test(){

  // stack
  printf("Creating Pepsi object from the stack ...\n");
  Pepsi v;
  Pepsi_init(&v);
  printf("name: %s\n", v.base.base.ops->name());
  printf("price: %f\n", v.base.base.ops->price());
  Packing* pack1 = v.base.base.ops->packing();
  printf("packing: %s\n", pack1->pack());
  Packing_delete(pack1);
  Pepsi_destroy(&v);
  // heap
  printf("Creating Pepsi object from the heap ...\n");
  Pepsi* p = Pepsi_new();
  printf("name: %s\n", p->base.base.ops->name());
  printf("price: %f\n", p->base.base.ops->price());
  Packing* pack2 = p->base.base.ops->packing();
  printf("packing: %s\n", pack2->pack());
  Packing_delete(pack2);
  Item_delete(&p->base.base);   // should call Pepsi_delete(Item*)
}


////////////////////////////////////////////////////////////////////////////////
//                                MEAL                                        //
////////////////////////////////////////////////////////////////////////////////

// it is assumed that meal objects takes ownership of item pointers
// which will need to be released as meal object is being destroyed.

typedef struct Meal_ Meal;
struct Meal_ {
  int count;                                // current number of items
  Item* _items[MAX_MEAL_ITEMS];             // array of item pointers
  void (*addItem)(Meal*,Item*);             // needs a 'this' pointer
  double (*getCost)(Meal*);                 // needs a 'this' pointer
  void (*showItems)(Meal*);                 // needs a 'this' pointer
};

void Meal_addItem(Meal* pObj,Item* item){
  assert(pObj != NULL);
  assert(item != NULL);
  if(pObj->count == MAX_MEAL_ITEMS){
    fprintf(stderr,"Meal::addItem : cannot add more items to meal\n");
    return;
  }
  pObj->_items[pObj->count++] = item;
}

double Meal_getCost(Meal* pObj){
  assert(pObj != NULL);
  double cost = 0.0;
  int i;
  for(i = 0; i < pObj->count; ++i){
    cost+=pObj->_items[i]->ops->price();
  }
  return cost;
}

void Meal_showItems(Meal* pObj){
  assert(pObj != NULL);
  int i;
  for(i = 0; i < pObj->count; ++i){
    printf("Item : %s", pObj->_items[i]->ops->name());
    Packing* packing = pObj->_items[i]->ops->packing();
    printf(", Packing : %s", packing->pack()); 
    Packing_delete(packing);
    printf(", Price : %f\n", pObj->_items[i]->ops->price());
  } 
}

void Meal_init(Meal* pObj){
  assert(pObj != NULL);
  pObj->count = 0;
  pObj->addItem = Meal_addItem;
  pObj->getCost = Meal_getCost;
  pObj->showItems = Meal_showItems;
  int i;
  for(i = 0; i <  MAX_MEAL_ITEMS; ++i){
    pObj->_items[i] = NULL;
  }
}
void Meal_destroy(Meal* pObj){
  assert(pObj != NULL);
  int i;
  for(i = 0; i < pObj->count; ++i){
    Item_delete(pObj->_items[i]);   // freeing item pointer. Meal has ownership
  }
  pObj->count =0;
  pObj->addItem = NULL;
  pObj->getCost = NULL;
  pObj->showItems = NULL;
  for(i = 0; i < MAX_MEAL_ITEMS; ++i){
    pObj->_items[i] = NULL;
  }
}

Meal* Meal_new(){
  Meal* pObj = (Meal*) malloc(sizeof(Meal));
  Meal_init(pObj);
  return pObj;
}

void Meal_delete(Meal* pObj){
  assert(pObj != NULL);
  Meal_destroy(pObj);
  free(pObj);
}

void Meal_test(){
  printf("Creating Meal object from the stack ...\n");
  // stack
  Meal m;
  Meal_init(&m);
  m.addItem(&m,&VegBurger_new()->base.base);
  m.addItem(&m,&ChickenBurger_new()->base.base);
  m.addItem(&m,&Coke_new()->base.base);
  m.addItem(&m,&Pepsi_new()->base.base);
  m.showItems(&m);
  Meal_destroy(&m);
}
////////////////////////////////////////////////////////////////////////////////
//                            MealBuilder                                     //
////////////////////////////////////////////////////////////////////////////////

typedef struct MealBuilder_ MealBuilder;
typedef struct MealBuilder_ MealBuilder;  // forward declaration needed
struct MealBuilder_{
  void* object;                         // pointer to concrete object
  void (*startNewMeal)(MealBuilder*);   // needs a 'this' pointer argument
  void (*addBurger)(MealBuilder*);      // needs a 'this' pointer argument
  void (*addDrink)(MealBuilder*);       // needs a 'this' pointer argument

};

////////////////////////////////////////////////////////////////////////////////
//                            DirectorCook                                    //
////////////////////////////////////////////////////////////////////////////////

// This is a concrete class
typedef struct DirectorCook_ DirectorCook;
struct DirectorCook_{
 // This is the main method of the director, which creates an object
  // based on some logic and algorithm which is encapsulated in the
  // method body, and uses the tools provided by the builder interface.
  void (*makeMeal)(DirectorCook*);  // needs a 'this' pointer argument
  // data
  MealBuilder* _builder;
};

void DirectorCook_makeMeal(DirectorCook* pObj){
  assert(pObj != NULL);
  assert(pObj->_builder != NULL);
  pObj->_builder->startNewMeal(pObj->_builder);
  pObj->_builder->addBurger(pObj->_builder);
  pObj->_builder->addDrink(pObj->_builder);
}



// Note that the manufacture algorithm contained in the director
// is very general and does not tell us anything about the type of
// the object being created, let alone its internal representation.

// We can implement MealBuilder in many different ways, so as to 
// construct objects of many possible types which do not even need
// to be related by a common base class 'Meal'

// However, at some point we need to retrieve the constructed object
// so there must be some method 'getObject'. In general, because the
// return type of 'getObject' may be arbitrary, the method declaration
// cannot be part of the interface MealBuilder as this would constrain
// the implementation to a specific type being constructed.

// In this example, we shall consider two concrete implementations of
// MealBuilder, a 'VegetarianMealBuilder' and a 'NonVegetarianMealBuilder'.
// Both implementation will allow the construction of objects of the same
// type, but one should remember that this need not be the case when 
// applying the builder design pattern.

// Concrete implementations of MealBuilder will hold a pointer to object
// of type Meal (the object being constructed), and will have a getObject().


typedef struct VegetarianMealBuilder_ VegetarianMealBuilder;
struct VegetarianMealBuilder_ {
  MealBuilder base;
  Meal* _meal;
  Meal* (*getMeal)(VegetarianMealBuilder*);
};

typedef struct NonVegetarianMealBuilder_ NonVegetarianMealBuilder;
struct NonVegetarianMealBuilder_ {
  MealBuilder base;
  Meal* _meal;
  Meal* (*getMeal)(NonVegetarianMealBuilder*);
};

// Initializing MealBuilder base object
void MealBuilder_Init(
    MealBuilder* pObj,                  // this
    void* object,                       // pointer to concrete object
    void (*startNewMeal)(MealBuilder*), // overriden virtual procedure
    void (*addBurger)(MealBuilder*),    // overriden virtual procedure
    void (*addDrink)(MealBuilder*)){    // overriden virtual procedure

  assert(pObj != NULL);
  pObj->object = object;
  pObj->startNewMeal = startNewMeal;
  pObj->addBurger = addBurger;
  pObj->addDrink = addDrink;
}

void MealBuilder_Destroy(MealBuilder* pObj){
  assert(pObj !=NULL);
  pObj->object = NULL;
  pObj->startNewMeal = NULL;
  pObj->addBurger = NULL;
  pObj->addDrink = NULL;
}

// initializing VegetarianMealBuilder object
void VegetarianMealBuilder_startNewMeal(MealBuilder* pObj){
}

void VegetarianMealBuilder_addBurger(MealBuilder* pObj){
}

void VegetarianMealBuilder_addDrink(MealBuilder* pObj){
}

Meal* VegetarianMealBuilder_getMeal(VegetarianMealBuilder* pObj){
  return NULL;
}

void VegetarianMealBuilder_Init(VegetarianMealBuilder* pObj){
  assert(pObj != NULL);
  // initializing base object
  MealBuilder_Init(
      &pObj->base, 
      (void*) pObj,
      VegetarianMealBuilder_startNewMeal,
      VegetarianMealBuilder_addBurger,
      VegetarianMealBuilder_addDrink);  // initializing base object
  // initializing derived object
  pObj->_meal = NULL;
  pObj->getMeal = VegetarianMealBuilder_getMeal;
}

void VegetarianMealBuilder_Destroy(VegetarianMealBuilder* pObj){
  assert(pObj != NULL);
  MealBuilder_Destroy(&pObj->base);
//  Meal_Delete(pObj->_meal); pObj->_meal = NULL;
  pObj->getMeal = NULL;
}

// initializing NonVegetarianMealBuilder object
void NonVegetarianMealBuilder_startNewMeal(MealBuilder* pObj){
}

void NonVegetarianMealBuilder_addBurger(MealBuilder* pObj){
}

void NonVegetarianMealBuilder_addDrink(MealBuilder* pObj){
}

Meal* NonVegetarianMealBuilder_getMeal(NonVegetarianMealBuilder* pObj){
  return NULL;
}

void NonVegetarianMealBuilder_Init(NonVegetarianMealBuilder* pObj){
  assert(pObj != NULL);
  // initializing base object
  MealBuilder_Init(
      &pObj->base, 
      (void*) pObj,
      NonVegetarianMealBuilder_startNewMeal,
      NonVegetarianMealBuilder_addBurger,
      NonVegetarianMealBuilder_addDrink);  // initializing base object
  // initializing derived object
  pObj->_meal = NULL;
  pObj->getMeal = NonVegetarianMealBuilder_getMeal;
}

void global_test(){
  //Wrapper_test();
  //Bottle_test();
  //VegBurger_test();
  //ChickenBurger_test();
  //Coke_test();
  //Pepsi_test();
  Meal_test();
}

int main(int argc, char* argv[]){
  // creating vegetarian meal
  // First we create the appropriate concrete builder

  // Next we create a director which will use this builder

  global_test();
  
  /*
  VegBurger* p = VegBurger_new();
  printf("%s\n",p->base.base.ops->name());
  printf("%s\n",p->base.base.ops->packing()->pack());
  printf("%f\n",p->base.base.ops->price());
  VegBurger_delete(p);
  */

  return 0;
}

