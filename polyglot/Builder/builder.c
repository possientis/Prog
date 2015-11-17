// Builder Design Pattern
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
// it is to manufacture meals, together with an interface 'MealBuilder'

////////////////////////////////////////////////////////////////////////////////
//                            MealBuilder                                     //
////////////////////////////////////////////////////////////////////////////////
typedef struct MealBuilder_ MealBuilder;

typedef struct MealBuilderOps_ MealBuilderOps;
struct MealBuilderOps_ {
  void (*startNewMeal)(MealBuilder*);   // needs a 'this' pointer argument
  void (*addBurger)(MealBuilder*);      // needs a 'this' pointer argument
  void (*addDrink)(MealBuilder*);       // needs a 'this' pointer argument
};


struct MealBuilder_{
  void* object;                         // pointer to concrete object
  void (*startNewMeal)(MealBuilder*);   // needs a 'this' pointer argument
  void (*addBurger)(MealBuilder*);      // needs a 'this' pointer argument
  void (*addDrink)(MealBuilder*);       // needs a 'this' pointer argument

};

typedef struct DirectorCook_ DirectorCook;
struct DirectorCook_{
  // data
  MealBuilder* _builder;
  // This is the main method of the director, which creates an object
  // based on some logic and algorithm which is encapsulated in the
  // method body, and uses the tools provided by the builder interface.
  void (*makeMeal)(DirectorCook*);  // needs a 'this' pointer argument
};


// needed to initialize DirectorCook function pointer
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

typedef struct Packing_ Packing;
struct Packing_ {
  void* object;                             // pointer to concrete object
  const char* (*pack)(Packing*);            // needs a 'this' pointer
};

typedef struct Wrapper_ Wrapper;
struct Wrapper_ {
  Packing base;
  const char* (*pack)(Wrapper*);            // needs a 'this' pointer
};

typedef struct Bottle_ Bottle;
struct Bottle_ {
  Packing base;
  const char* (*pack)(Bottle*);            // needs a 'this' pointer
};

typedef struct Item_ Item;
struct Item_ {
  void* object;                             // pointer to concrete object
  double (*price)(Item*);                   // needs a 'this' pointer
  const char* (*name)(Item*);               // needs a 'this' pointer 
  Packing* (*packing)(Item*);               // needs a 'this' pointer
};


typedef struct Burger_ Burger;
struct Burger_ {
  Item base;
  Packing* (*packing)(Burger*);             // needs a 'this' pointer
};

typedef struct ColdDrink_ ColdDrink;
struct ColdDrink_ {
  Item base;
  Packing* (*packing)(ColdDrink*);          // needs a 'this' pointer
};

typedef struct VegBurger_ VegBurger;
struct VegBurger_ {
  Burger base;
  double (*price)(VegBurger*);              // needs a 'this' pointer
  const char* (*name)(VegBurger*);          // needs a 'this' pointer 
};

typedef struct ChickenBurger_ ChickenBurger;
struct ChickenBurger_ {
  Burger base;
  double (*price)(ChickenBurger*);          // needs a 'this' pointer
  const char* (*name)(ChickenBurger*);      // needs a 'this' pointer 
};

typedef struct Coke_ Coke;
struct Coke_ {
  ColdDrink base;
  double (*price)(Coke*);                   // needs a 'this' pointer
  const char* (*name)(Coke*);               // needs a 'this' pointer 
};

typedef struct Pepsi_ Pepsi;
struct Pepsi_ {
  ColdDrink base;
  double (*price)(Pepsi*);                  // needs a 'this' pointer
  const char* (*name)(Pepsi*);              // needs a 'this' pointer 
};

typedef struct Meal_ Meal;
struct Meal_ {
  Item* _items;
  void (*addItem)(Meal*,Item*);             // needs a 'this' pointer
  double (*getCost)(Meal*);                 // needs a 'this' pointer
  void (*showItems)(Meal*);                 // needs a 'this' pointer
};

// initializing Meal object
void Meal_addItem(Meal* pObj,Item* item){
}
double Meal_getCost(Meal* pObj){
  return 0.0;
}
void Meal_showItems(Meal* pObj){
}
void Meal_Init(Meal* pObj){
  assert(pObj != NULL);
  pObj->_items = NULL;
  pObj->addItem = Meal_addItem;
  pObj->getCost = Meal_getCost;
  pObj->showItems = Meal_showItems;
}
void Meal_Destroy(Meal* pObj){
  assert(pObj != NULL);
}

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

int main(int argc, char* argv[]){
  // creating vegetarian meal
  // First we create the appropriate concrete builder
  VegetarianMealBuilder vegBuilder;
  VegetarianMealBuilder_Init(&vegBuilder);
  // Next we create a director which will use this builder

  VegetarianMealBuilder_Destroy(&vegBuilder);

  return 0;
}

