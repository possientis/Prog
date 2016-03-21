// Decorator Design Pattern

#include <stdio.h>
#include <assert.h>
#include <malloc.h>
#include <string.h>

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
//  fprintf(stderr, message, ptr);
  memory_check ^= (long) ptr;
  return 0L;
}

/******************************************************************************/
/*                               VirtualTable                                 */
/******************************************************************************/

struct VirtualTable_ {
  int count;    // reference count
  void          (*description)(void* self, char* outbuf, size_t size);
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
    void        (*description)(void*, char*, size_t),
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

VirtualTable* Pizza_VirtualTable_new();               // forward
VirtualTable* PlainPizza_VirtualTable_new();          // forward
VirtualTable* PizzaDecorator_VirtualTable_new();      // forward
VirtualTable* WithExtraCheese_VirtualTable_new();     // forward
VirtualTable* WithExtraOlives_VirtualTable_new();     // forward
VirtualTable* WithExtraAnchovies_VirtualTable_new();  // forward

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
          instance[WITH_EXTRA_CHEESE] = WithExtraCheese_VirtualTable_new();
          assert(instance[WITH_EXTRA_CHEESE] != NULL);
          break;
        case WITH_EXTRA_OLIVES:
          instance[WITH_EXTRA_OLIVES] = WithExtraOlives_VirtualTable_new();
          assert(instance[WITH_EXTRA_OLIVES] != NULL);
          break;
        case WITH_EXTRA_ANCHOVIES:
          instance[WITH_EXTRA_ANCHOVIES] = WithExtraAnchovies_VirtualTable_new();
          assert(instance[WITH_EXTRA_ANCHOVIES] != NULL);
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

void _Pizza_description(void* self, char* buffer, size_t size){
  assert(self != NULL);
  assert(buffer != NULL);
  fprintf(stderr, "Pizza::description is not implemented\n");
  strncpy(buffer, "Pizza::description is not implemented", size);
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

void _PlainPizza_description(void* self, char* buffer, size_t size){
  assert(self != NULL);
  assert(buffer != NULL);
  strncpy(buffer, "Plain pizza",size);
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

void  Pizza_description(Pizza*, char*, size_t);  // forward
void _PizzaDecorator_description(void* self, char* buffer, size_t size){
  assert(self != NULL);
  assert(buffer != NULL);
  PizzaDecorator* object = (PizzaDecorator*) self;
  assert(object->_pizza != NULL);
  Pizza_description(object->_pizza, buffer, size);   // polymorphic call
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

struct WithExtraCheese_ {
  PizzaDecorator base;
};


void _WithExtraCheese_description(void* self, char* buffer, size_t size){
  assert(self != NULL);
  assert(buffer != NULL);
  PizzaDecorator* object = (PizzaDecorator*) self;
  assert(object->_pizza != NULL);
  Pizza_description(object->_pizza, buffer, size);
  size_t length = strlen(buffer);
  size_t newsize = size - length;
  strncat(buffer, " + extra cheese", newsize);
}

double _WithExtraCheese_cost(void* self){
  assert(self != NULL);
  PizzaDecorator* object = (PizzaDecorator*) self;
  assert(object->_pizza != NULL);
  return Pizza_cost(object->_pizza) + 0.5;         // polymorphic call
}

void _WithExtraCheese_delete(void* self){
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
    memory_log("Deallocating existing with extra cheese object %lx\n", self);
    free(self);
  }
  else {
    memory_log("Deleting copy of with extra cheese object %lx\n", self);
  }
}

VirtualTable* WithExtraCheese_VirtualTable_new(){
  return VirtualTable_new(_WithExtraCheese_description, 
                          _WithExtraCheese_cost, 
                          _WithExtraCheese_delete);
}

/******************************************************************************/
/*                      WithExtraOlives virtual table                          */
/******************************************************************************/

struct WithExtraOlives_ {
  PizzaDecorator base;
};


void _WithExtraOlives_description(void* self, char* buffer, size_t size){
  assert(self != NULL);
  assert(buffer != NULL);
  PizzaDecorator* object = (PizzaDecorator*) self;
  assert(object->_pizza != NULL);
  Pizza_description(object->_pizza, buffer, size);
  size_t length = strlen(buffer);
  size_t newsize = size - length;
  strncat(buffer, " + extra olives", newsize);
}

double _WithExtraOlives_cost(void* self){
  assert(self != NULL);
  PizzaDecorator* object = (PizzaDecorator*) self;
  assert(object->_pizza != NULL);
  return Pizza_cost(object->_pizza) + 0.7;         // polymorphic call
}

void _WithExtraOlives_delete(void* self){
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
    memory_log("Deallocating existing with extra olives object %lx\n", self);
    free(self);
  }
  else {
    memory_log("Deleting copy of with extra olives object %lx\n", self);
  }
}

VirtualTable* WithExtraOlives_VirtualTable_new(){
  return VirtualTable_new(_WithExtraOlives_description, 
                          _WithExtraOlives_cost, 
                          _WithExtraOlives_delete);
}




/******************************************************************************/
/*                      WithExtraAnchovies virtual table                      */
/******************************************************************************/

struct WithExtraAnchovies_ {
  PizzaDecorator base;
};


void _WithExtraAnchovies_description(void* self, char* buffer, size_t size){
  assert(self != NULL);
  assert(buffer != NULL);
  PizzaDecorator* object = (PizzaDecorator*) self;
  assert(object->_pizza != NULL);
  Pizza_description(object->_pizza, buffer, size);
  size_t length = strlen(buffer);
  size_t newsize = size - length;
  strncat(buffer, " + extra anchovies", newsize);
}

double _WithExtraAnchovies_cost(void* self){
  assert(self != NULL);
  PizzaDecorator* object = (PizzaDecorator*) self;
  assert(object->_pizza != NULL);
  return Pizza_cost(object->_pizza) + 0.8;         // polymorphic call
}

void _WithExtraAnchovies_delete(void* self){
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
    memory_log("Deallocating existing with extra anchovies object %lx\n", self);
    free(self);
  }
  else {
    memory_log("Deleting copy of with extra anchovies object %lx\n", self);
  }
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
void Pizza_description(Pizza* self, char* buffer, size_t size){
  assert(self != NULL);
  assert(buffer != NULL);
  VirtualTable* vtable = self->vtable;
  assert(vtable != NULL);
  void (*description)(void*, char*, size_t);
  description = vtable->description;
  assert(description != NULL);
  description(self, buffer, size);
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
void PlainPizza_description(PlainPizza* self, char* buffer, size_t size){
  assert(self != NULL);
  assert(buffer != NULL);
  Pizza* pizza = (Pizza*) self;           // upcast
  VirtualTable* vtable = pizza->vtable;
  assert(vtable != NULL);
  void (*description)(void*, char*, size_t);
  description = vtable->description;
  assert(description != NULL);
  description(self, buffer, size);
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
void PizzaDecorator_description(PizzaDecorator* self, char* buffer, size_t size){
  assert(self != NULL);
  assert(buffer != NULL);
  Pizza* pizza = (Pizza*) self;           // upcast
  VirtualTable* vtable = pizza->vtable;
  assert(vtable != NULL);
  void (*description)(void*, char*, size_t);
  description = vtable->description;
  assert(description != NULL);
  description(self, buffer, size);
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
/*                                WithExtraCheese                             */
/******************************************************************************/

WithExtraCheese* WithExtraCheese_copy(WithExtraCheese* self){
  assert(self != NULL);
  memory_log("Making copy of with extra cheese object %lx\n", self);
  Pizza* pizza = (Pizza*) self;           // upcast
  pizza->count++;
  return self;
}


// WithExtraCheese object takes ownership of argument pizza object
WithExtraCheese* WithExtraCheese_new(Pizza* pizza){
  assert(pizza != NULL);
  WithExtraCheese* ptr = (WithExtraCheese*) malloc(sizeof(WithExtraCheese));
  assert(ptr != NULL);
  memory_log("Allocating new with extra cheese object %lx\n", ptr);
  Pizza* base = (Pizza *) ptr;                      // upcast
  base->count = 1;
  base->vtable = VirtualTable_instance(WITH_EXTRA_CHEESE, 0);
  assert(base->vtable != NULL);
  PizzaDecorator* decor = (PizzaDecorator*) ptr;    // upcast
  decor->_pizza = pizza;
  return ptr;
}

// boiler-plate, managing virtual table indirection
void WithExtraCheese_delete(WithExtraCheese* self){ // virtual
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
void WithExtraCheese_description(WithExtraCheese* self, char* buffer, size_t size){
  assert(self != NULL);
  assert(buffer != NULL);
  Pizza* pizza = (Pizza*) self;           // upcast
  VirtualTable* vtable = pizza->vtable;
  assert(vtable != NULL);
  void (*description)(void*, char*, size_t);
  description = vtable->description;
  assert(description != NULL);
  description(self, buffer, size);
}

// boiler-plate, managing virtual table indirection
double WithExtraCheese_cost(WithExtraCheese* self){
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
/*                                WithExtraOlives                             */
/******************************************************************************/

WithExtraOlives* WithExtraOlives_copy(WithExtraOlives* self){
  assert(self != NULL);
  memory_log("Making copy of with extra olives object %lx\n", self);
  Pizza* pizza = (Pizza*) self;           // upcast
  pizza->count++;
  return self;
}


// WithExtraOlives object takes ownership of argument pizza object
WithExtraOlives* WithExtraOlives_new(Pizza* pizza){
  assert(pizza != NULL);
  WithExtraOlives* ptr = (WithExtraOlives*) malloc(sizeof(WithExtraOlives));
  assert(ptr != NULL);
  memory_log("Allocating new with extra olives object %lx\n", ptr);
  Pizza* base = (Pizza *) ptr;                      // upcast
  base->count = 1;
  base->vtable = VirtualTable_instance(WITH_EXTRA_OLIVES, 0);
  assert(base->vtable != NULL);
  PizzaDecorator* decor = (PizzaDecorator*) ptr;    // upcast
  decor->_pizza = pizza;
  return ptr;
}

// boiler-plate, managing virtual table indirection
void WithExtraOlives_delete(WithExtraOlives* self){ // virtual
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
void WithExtraOlives_description(WithExtraOlives* self, char* buffer, size_t size){
  assert(self != NULL);
  assert(buffer != NULL);
  Pizza* pizza = (Pizza*) self;           // upcast
  VirtualTable* vtable = pizza->vtable;
  assert(vtable != NULL);
  void (*description)(void*, char*, size_t);
  description = vtable->description;
  assert(description != NULL);
  description(self, buffer, size);
}

// boiler-plate, managing virtual table indirection
double WithExtraOlives_cost(WithExtraOlives* self){
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
/*                                WithExtraAnchovies                             */
/******************************************************************************/

WithExtraAnchovies* WithExtraAnchovies_copy(WithExtraAnchovies* self){
  assert(self != NULL);
  memory_log("Making copy of with extra anchovies object %lx\n", self);
  Pizza* pizza = (Pizza*) self;           // upcast
  pizza->count++;
  return self;
}


// WithExtraAnchovies object takes ownership of argument pizza object
WithExtraAnchovies* WithExtraAnchovies_new(Pizza* pizza){
  assert(pizza != NULL);
  WithExtraAnchovies* ptr = (WithExtraAnchovies*) malloc(sizeof(WithExtraAnchovies));
  assert(ptr != NULL);
  memory_log("Allocating new with extra anchovies object %lx\n", ptr);
  Pizza* base = (Pizza *) ptr;                      // upcast
  base->count = 1;
  base->vtable = VirtualTable_instance(WITH_EXTRA_ANCHOVIES, 0);
  assert(base->vtable != NULL);
  PizzaDecorator* decor = (PizzaDecorator*) ptr;    // upcast
  decor->_pizza = pizza;
  return ptr;
}

// boiler-plate, managing virtual table indirection
void WithExtraAnchovies_delete(WithExtraAnchovies* self){ // virtual
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
void WithExtraAnchovies_description(WithExtraAnchovies* self, char* buffer, size_t size){
  assert(self != NULL);
  assert(buffer != NULL);
  Pizza* pizza = (Pizza*) self;           // upcast
  VirtualTable* vtable = pizza->vtable;
  assert(vtable != NULL);
  void (*description)(void*, char*, size_t);
  description = vtable->description;
  assert(description != NULL);
  description(self, buffer, size);
}

// boiler-plate, managing virtual table indirection
double WithExtraAnchovies_cost(WithExtraAnchovies* self){
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

  Pizza* plainPizza   = (Pizza*) PlainPizza_new();

  Pizza* nicePizza    = (Pizza*) WithExtraCheese_new(
                        (Pizza*) PlainPizza_new()); 

  Pizza* superPizza   = (Pizza*) WithExtraOlives_new(
                        (Pizza*) WithExtraCheese_new(
                        (Pizza*) PlainPizza_new())); 

  Pizza* ultraPizza   = (Pizza*) WithExtraAnchovies_new(
                        (Pizza*) WithExtraOlives_new(
                        (Pizza*) WithExtraCheese_new(
                        (Pizza*) PlainPizza_new()))); 

  char buffer[128];   //  string output

  Pizza_description(plainPizza, buffer, 128);
  printf("Plain Pizza: \tCost: %0.1f\tDescription: %s\n", 
    Pizza_cost(plainPizza), buffer);

  Pizza_description(nicePizza, buffer, 128);
  printf("Nice Pizza: \tCost: %0.1f\tDescription: %s\n", 
    Pizza_cost(nicePizza), buffer);

  Pizza_description(superPizza, buffer, 128);
  printf("Super Pizza: \tCost: %0.1f\tDescription: %s\n", 
    Pizza_cost(superPizza), buffer);

  Pizza_description(ultraPizza, buffer, 128);
  printf("Ultra Pizza: \tCost: %0.1f\tDescription: %s\n", 
    Pizza_cost(ultraPizza), buffer);

  // objects deallocation
  Pizza_delete(ultraPizza);
  Pizza_delete(superPizza);
  Pizza_delete(nicePizza);
  Pizza_delete(plainPizza);

  // final virtual tables deallocation
  VirtualTable_instance(WITH_EXTRA_ANCHOVIES,1);
  VirtualTable_instance(WITH_EXTRA_OLIVES,1);
  VirtualTable_instance(WITH_EXTRA_CHEESE,1);
  VirtualTable_instance(PLAIN_PIZZA,1);

  assert(memory_log(NULL,NULL) == 0L);  // no memory leak detected
  return 0;
}

