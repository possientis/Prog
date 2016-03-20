// Decorator Design Pattern

#include <stdio.h>
#include <assert.h>
#include <malloc.h>

#define NUM_TOTAL_TYPES 6   // number of sub-types of Pizza
typedef enum {PIZZA = 0,
              PLAIN_PIZZA = 1,
              PIZZA_DECORATOR = 2,
              WITH_EXTRA_CHEESE = 3,
              WITH_EXTRA_OLIVES = 4,
              WITH_EXTRA_ANCHOVIES = 5 } PizzaType;

typedef struct VirtualTable_        VirtualTable;
typedef struct Pizza_               Pizza;  
typedef struct PlainPizza_          PlainPizza;
typedef struct PizzaDecorator_      PizzaDecorator;
typedef struct WithExtraCheese_     WithExtraCheese;
typedef struct WithExtraOlives_     WithExtraOlives;
typedef struct WithExtraAnchovies_  WithExtraAnchovies;

long memory_log(const char* message, const void* ptr){
  static long memory_check = 0L;
  if(message == NULL && ptr == NULL) return memory_check;
  assert(message != NULL);
  assert(ptr != NULL);
  fprintf(stderr, message, ptr);
  memory_check ^= (long) ptr;
  return 0L;
}

/******************************************************************************/
/*                               VirtualTable                                 */
/******************************************************************************/

struct VirtualTable_ {
  int count;    // reference count
  const char*   (*description)(void* self);
  double        (*cost)(void* self);
  void          (*delete)(void* self);
};

VirtualTable* VirtualTable_copy(VirtualTable* self){
  assert(self != NULL);
  memory_log("Making copy of virtual table %lx\n", self);
  self->count++;
  return self;
}

VirtualTable* VirtualTable_new(
    const char* (*description)(void*),
    double      (*cost)(void*),
    void        (*delete)(void*)){

  assert(description != NULL);
  assert(cost != NULL);
  assert(delete != NULL);
  VirtualTable* ptr = (VirtualTable*) malloc(sizeof(VirtualTable));
  memory_log("Allocating new virtual table %lx\n", ptr);
  assert(ptr != NULL);
  ptr->count        = 1; // first reference
  ptr->description  = description;
  ptr->cost         = cost;
  ptr->delete       = delete;
  return ptr;
}
  
void VirtualTable_delete(VirtualTable* self){
  assert(self != NULL);
  assert(self->count > 0);
  self->count--;
  if(self->count == 0){ // deallocation needed
    self->description = NULL;
    self->cost        = NULL;
    self->delete      = NULL;
    memory_log("Deallocating existing virtual table %lx\n", self);
    free(self);
  }
  else                { // just logging
    memory_log("Deleting copy of virtual table %lx\n", self);
  }
}

// This function returns the singleton instance of the virtual table associated
// with the subtype of Pizza provided as argument. Use release_flag = 0 (false)
// for the standard call. This function returns NULL when release_flag = 1 (true),
// in which case the virtual table instance for the specified type is deallocated.
// This should only be done when all other copies of the virtual table instance
// have been deleted.

VirtualTable* Pizza_VirtualTable_new();           // forward
VirtualTable* PlainPizza_VirtualTable_new();      // forward
VirtualTable* PizzaDecorator_VirtualTable_new();  // forward

VirtualTable* VirtualTable_instance(PizzaType type, int release_flag){
  static VirtualTable* instance[NUM_TOTAL_TYPES];
  assert(release_flag == 0 || release_flag == 1);
  assert(0 <= type && type < NUM_TOTAL_TYPES);
  if(release_flag == 1){                // need to release instance for type
    assert(instance[type] != NULL);
    assert(instance[type]->count == 1); // should be done last
    VirtualTable_delete(instance[type]);
    instance[type] == NULL;
    return NULL;
  }
  else{                                 // returning instance for type
    if(instance[type] == NULL){
      switch(type){
        case PIZZA:
          instance[PIZZA] = Pizza_VirtualTable_new();
          assert(instance[PIZZA] != NULL);
          break;
        case PLAIN_PIZZA:
          instance[PLAIN_PIZZA] = PlainPizza_VirtualTable_new();
          assert(instance[PLAIN_PIZZA] != NULL);
          break;
        case PIZZA_DECORATOR:
          instance[PIZZA_DECORATOR] = PizzaDecorator_VirtualTable_new();
          assert(instance[PIZZA_DECORATOR] != NULL);
          break;
        case WITH_EXTRA_CHEESE:
          assert(NULL);
          break;
        case WITH_EXTRA_OLIVES:
          assert(NULL);
          break;
        case WITH_EXTRA_ANCHOVIES:
          assert(NULL);
          break;
        default:
          assert(NULL);
      }
    }
    assert(instance[type] != NULL);
    return VirtualTable_copy(instance[type]);
  }

}

void VirtualTable_ReleaseAll(){
}

/******************************************************************************/
/*                            Pizza virtual table                             */
/******************************************************************************/

struct Pizza_ {
  int count;              // reference count
  VirtualTable* vtable;
};

const char* _Pizza_description(void* self){
  assert(self != NULL);
  fprintf(stderr, "Pizza::description is not implemented\n");
  return "Pizza::description is not implemented";

}

double _Pizza_cost(void* self){
  assert(self != NULL);
  fprintf(stderr,"Pizza::cost is not implemented\n");
  return 0.0;
}

void _Pizza_delete(void* self){
  assert(self != 0);
  Pizza* object = (Pizza*) self;
  object->count--;
  if(object->count == 0){
    VirtualTable* vtable = object->vtable;
    assert(vtable != NULL);
    VirtualTable_delete(vtable);
    memory_log("Deallocating existing pizza %lx\n", object);
    free(object);
  }
  else {
    memory_log("Deleting copy of pizza %lx\n", object);
  }
}

VirtualTable* Pizza_VirtualTable_new(){
  return VirtualTable_new(_Pizza_description, _Pizza_cost, _Pizza_delete);
}


/******************************************************************************/
/*                          PlainPizza virtual table                          */
/******************************************************************************/

struct PlainPizza_ {
  Pizza base;
}; 

const char* _PlainPizza_description(void* self){
  return "Plain pizza";
}

double _PlainPizza_cost(void* self){
  return 3.0;
}

void _PlainPizza_delete(void* self){
  assert(self != 0);
  Pizza* pizza = (Pizza*) self;
  pizza->count--;
  if(pizza->count == 0){
    VirtualTable* vtable = pizza->vtable;
    assert(vtable != NULL);
    VirtualTable_delete(vtable);
    memory_log("Deallocating existing plain pizza %lx\n", pizza);
    free(pizza);
  }
  else {
    memory_log("Deleting copy of pizza %lx\n", pizza);
  }
}

VirtualTable* PlainPizza_VirtualTable_new(){
  return VirtualTable_new(_PlainPizza_description, 
                          _PlainPizza_cost, 
                          _PlainPizza_delete);
}


/******************************************************************************/
/*                      PizzaDecorator virtual table                          */
/******************************************************************************/

struct PizzaDecorator_ {
  Pizza base;               // just virtual table and reference count
  Pizza* _pizza;            // decorated pizza
};

const char* Pizza_description(Pizza*);        // forward
const char* _PizzaDecorator_description(void* self){
  assert(self != NULL);
  PizzaDecorator* object = (PizzaDecorator*) self;
  assert(object->_pizza != NULL);
  return Pizza_description(object->_pizza);   // polymorphic call
}

double Pizza_cost(Pizza*);                    // forward
double _PizzaDecorator_cost(void* self){
  assert(self != NULL);
  PizzaDecorator* object = (PizzaDecorator*) self;
  assert(object->_pizza != NULL);
  return Pizza_cost(object->_pizza);         // polymorphic call
}

void Pizza_delete(Pizza*);
void _PizzaDecorator_delete(void* self){
  assert(self != NULL);
  Pizza* base = (Pizza*) self;
  base->count--;
  if(base->count == 0){
    VirtualTable* vtable = base->vtable;
    assert(vtable != NULL);
    VirtualTable_delete(vtable);
    PizzaDecorator* object = (PizzaDecorator*) self;
    Pizza* pizza = object->_pizza;
    assert(pizza != NULL);
    Pizza_delete(pizza);                     // polymorphic call
    memory_log("Deallocating existing pizza decorator %lx\n", self);
    free(self);
  }
  else {
    memory_log("Deleting copy of pizza decorator %lx\n", self);
  }

}

VirtualTable* PizzaDecorator_VirtualTable_new(){
  return VirtualTable_new(_PizzaDecorator_description, 
                          _PizzaDecorator_cost, 
                          _PizzaDecorator_delete);
}


/******************************************************************************/
/*                      WithExtraCheese virtual table                          */
/******************************************************************************/
const char* _WithExtraCheese_description(void* self){
  // TBI
}

double _WithExtraCheese_cost(void* self){
  // TBI
}

void _WithExtraCheese_delete(void* self){
  // TBI
}

VirtualTable* WithExtraCheese_VirtualTable_new(){
  return VirtualTable_new(_WithExtraCheese_description, 
                          _WithExtraCheese_cost, 
                          _WithExtraCheese_delete);
}

/******************************************************************************/
/*                      WithExtraOlives virtual table                          */
/******************************************************************************/
const char* _WithExtraOlives_description(void* self){
  // TBI
}

double _WithExtraOlives_cost(void* self){
  // TBI
}

void _WithExtraOlives_delete(void* self){
  // TBI
}

VirtualTable* WithExtraOlives_VirtualTable_new(){
  return VirtualTable_new(_WithExtraOlives_description, 
                          _WithExtraOlives_cost, 
                          _WithExtraOlives_delete);
}

/******************************************************************************/
/*                      WithExtraAnchovies virtual table                          */
/******************************************************************************/
const char* _WithExtraAnchovies_description(void* self){
  // TBI
}

double _WithExtraAnchovies_cost(void* self){
  // TBI
}

void _WithExtraAnchovies_delete(void* self){
  // TBI
}

VirtualTable* WithExtraAnchovies_VirtualTable_new(){
  return VirtualTable_new(_WithExtraAnchovies_description, 
                          _WithExtraAnchovies_cost, 
                          _WithExtraAnchovies_delete);
}

/******************************************************************************/
/*                               Pizza                                        */
/******************************************************************************/

Pizza* Pizza_copy(Pizza* self){
  assert(self != NULL);
  self->count++;
  memory_log("Making copy of pizza %lx\n", self);
  return self;
}

Pizza* Pizza_new(){
  Pizza* ptr = (Pizza*) malloc(sizeof(Pizza));
  assert(ptr != NULL);
  memory_log("Allocating new pizza %lx\n", ptr);
  ptr->count = 1;
  ptr->vtable = VirtualTable_instance(PIZZA,0);
  assert(ptr->vtable != NULL);
  return ptr;
}

// boiler-plate, managing virtual table indirection
void Pizza_delete(Pizza* self){ // virtual
  assert(self != NULL);
  VirtualTable* vtable = self->vtable;
  assert(vtable != NULL);
  void (*delete)(void*);
  delete = vtable->delete;
  assert(delete != NULL);
  delete(self); // calling virtual destructor
} 

// boiler-plate, managing virtual table indirection
const char* Pizza_description(Pizza* self){
  assert(self != NULL);
  VirtualTable* vtable = self->vtable;
  assert(vtable != NULL);
  const char* (*description)(void*);
  description = vtable->description;
  assert(description != NULL);
  return description(self);
}

// boiler-plate, managing virtual table indirection
double Pizza_cost(Pizza* self){
  assert(self != NULL);
  VirtualTable* vtable = self->vtable;
  assert(vtable != NULL);
  double (*cost)(void*);
  cost = vtable->cost;
  assert(cost != NULL);
  return cost((void*) self);
}

/******************************************************************************/
/*                               PlainPizza                                   */
/******************************************************************************/

PlainPizza* PlainPizza_copy(PlainPizza* self){
  assert(self != NULL);
  memory_log("Making copy of plain pizza %lx\n", self);
  Pizza* pizza = (Pizza*) self;           // upcast
  pizza->count++;
  return self;
}

PlainPizza* PlainPizza_new(){
  PlainPizza* ptr = (PlainPizza*) malloc(sizeof(PlainPizza));
  assert(ptr != NULL);
  memory_log("Allocating new plain pizza %lx\n", ptr);
  Pizza* pizza = (Pizza *) ptr;           // upcast
  pizza->count = 1;
  pizza->vtable = VirtualTable_instance(PLAIN_PIZZA, 0);
  assert(pizza->vtable != NULL);
  return ptr;
}

// boiler-plate, managing virtual table indirection
void PlainPizza_delete(PlainPizza* self){ // virtual
  assert(self != NULL);
  Pizza* pizza = (Pizza*) self;           // upcast
  VirtualTable* vtable = pizza->vtable;
  assert(vtable != NULL);
  void (*delete)(void*);
  delete = vtable->delete;
  assert(delete != NULL);
  delete(self); // calling virtual destructor
}

// boiler-plate, managing virtual table indirection
const char* PlainPizza_description(PlainPizza* self){
  assert(self != NULL);
  Pizza* pizza = (Pizza*) self;           // upcast
  VirtualTable* vtable = pizza->vtable;
  assert(vtable != NULL);
  const char* (*description)(void*);
  description = vtable->description;
  assert(description != NULL);
  return description(self);
}

// boiler-plate, managing virtual table indirection
double PlainPizza_cost(PlainPizza* self){
  assert(self != NULL);
  Pizza* pizza = (Pizza*) self;
  VirtualTable* vtable = pizza->vtable;
  assert(vtable != NULL);
  double (*cost)(void*);
  cost = vtable->cost;
  assert(cost != NULL);
  return cost((void*) self);
}

/******************************************************************************/
/*                                PizzaDecorator                              */
/******************************************************************************/

PizzaDecorator* PizzaDecorator_copy(PizzaDecorator* self){
  assert(self != NULL);
  memory_log("Making copy of pizza decorator %lx\n", self);
  Pizza* pizza = (Pizza*) self;           // upcast
  pizza->count++;
  return self;
}


// PizzaDecorator object takes ownership of argument pizza object
PizzaDecorator* PizzaDecorator_new(Pizza* pizza){
  assert(pizza != NULL);
  PizzaDecorator* ptr = (PizzaDecorator*) malloc(sizeof(PizzaDecorator));
  assert(ptr != NULL);
  memory_log("Allocating new pizza decorator %lx\n", ptr);
  Pizza* base = (Pizza *) ptr;           // upcast
  base->count = 1;
  base->vtable = VirtualTable_instance(PIZZA_DECORATOR, 0);
  assert(base->vtable != NULL);
  ptr->_pizza = pizza;
  return ptr;
}

// boiler-plate, managing virtual table indirection
void PizzaDecorator_delete(PizzaDecorator* self){ // virtual
  assert(self != NULL);
  Pizza* pizza = (Pizza*) self;           // upcast
  VirtualTable* vtable = pizza->vtable;
  assert(vtable != NULL);
  void (*delete)(void*);
  delete = vtable->delete;
  assert(delete != NULL);
  delete(self); // calling virtual destructor
}
//
// boiler-plate, managing virtual table indirection
const char* PizzaDecorator_description(PizzaDecorator* self){
  assert(self != NULL);
  Pizza* pizza = (Pizza*) self;           // upcast
  VirtualTable* vtable = pizza->vtable;
  assert(vtable != NULL);
  const char* (*description)(void*);
  description = vtable->description;
  assert(description != NULL);
  return description(self);
}

// boiler-plate, managing virtual table indirection
double PizzaDecorator_cost(PizzaDecorator* self){
  assert(self != NULL);
  Pizza* pizza = (Pizza*) self;
  VirtualTable* vtable = pizza->vtable;
  assert(vtable != NULL);
  double (*cost)(void*);
  cost = vtable->cost;
  assert(cost != NULL);
  return cost((void*) self);
}


/******************************************************************************/
/*                                    Main                                    */
/******************************************************************************/

int main(){

  PlainPizza* pizza = PlainPizza_new();
  PizzaDecorator* decor = PizzaDecorator_new((Pizza*) pizza);

  printf("Pizza::description: %s\n", Pizza_description((Pizza*) decor));
  printf("PizzaDecorator::description: %s\n", PizzaDecorator_description(decor));
  printf("Pizza::cost: %f\n", Pizza_cost((Pizza*) decor));
  printf("PizzaDecorator::cost: %f\n", PizzaDecorator_cost(decor));


  PizzaDecorator_delete(decor);

  VirtualTable_instance(PIZZA_DECORATOR,1);
  VirtualTable_instance(PLAIN_PIZZA,1);
  assert(memory_log(NULL,NULL) == 0L);  // no memory leak detected
  return 0;
}

