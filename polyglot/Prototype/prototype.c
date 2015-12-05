// Prototype design pattern
// Imagine that in order to instantiate certain objects we need to carry out
// expensive database queries. In order to improve performance, it would 
// be beneficial to cache whatever object is created from the database
// and return a copy of the cached object whenever a subsequent request
// for object instantiation arises.
#include <memory.h>
#include <stdio.h>
#include <assert.h>
#include <malloc.h>

////////////////////////////////////////////////////////////////////////////////
//                                Cloneable                                   //
////////////////////////////////////////////////////////////////////////////////

typedef struct Cloneable_ Cloneable;
struct Cloneable_ {
  void* object;
  void (*delete)(Cloneable*);       // virtual
  Cloneable* (*clone)(Cloneable*);  // virtual
};

void Cloneable_init(
    Cloneable* ptr,
    void* object,
    void (*delete)(Cloneable*),
    Cloneable* (*clone)(Cloneable*)
    ){
  assert(ptr != NULL);
  ptr->object = object;
  ptr-> delete = delete;
  ptr-> clone = clone;
}

void Cloneable_destroy(Cloneable* ptr){
  assert(ptr != NULL);
  ptr->object = NULL;
  ptr->delete = NULL;
  ptr->clone = NULL;
}

void Cloneable_delete(Cloneable* ptr){
  assert(ptr != NULL);
  void (*delete)(Cloneable* ptr);
  delete = ptr->delete;
  if (delete == NULL){ // not a derived object
    Cloneable_destroy(ptr);
    free(ptr);
  }
  else{
    delete(ptr);  // calling virtual delete
  }
}

Cloneable* Cloneable_clone(Cloneable* self){
  fprintf(stderr,"Cloneable::clone is not implemented\n");
  return NULL;
}

Cloneable* Cloneable_new(){
  Cloneable* ptr = (Cloneable*) malloc(sizeof(Cloneable));
  Cloneable_init(ptr, ptr, NULL, Cloneable_clone);
  assert(ptr != NULL);
  assert(ptr->object == ptr);
  assert(ptr->delete == NULL);  // this is a base object, field should be NULL
  assert(ptr->clone == Cloneable_clone);
  return ptr;
}

void Cloneable_test(){
  Cloneable* ptr = Cloneable_new();
  ptr->clone(ptr);
  Cloneable_delete(ptr);
}

////////////////////////////////////////////////////////////////////////////////
//                                Shape                                       //
////////////////////////////////////////////////////////////////////////////////

#define SHAPE_MAX_ID_LENGTH 32
typedef struct Shape_ Shape;
struct Shape_ {
  Cloneable base;
  char* (*getID)(Shape*);                 // not virtual
  void (*setID)(Shape*, const char* id);  // not virtual
  void (*draw)(Shape*);                   // virtual
  char buffer[SHAPE_MAX_ID_LENGTH];       // not space efficient but simple
};

char* Shape_getID(Shape* self){
  assert(self != NULL);
  return self->buffer;
}

void Shape_setID(Shape* self, const char* id){
  assert(self != NULL);
  assert(id != NULL);
  assert(strlen(id) < SHAPE_MAX_ID_LENGTH - 1);
  strcpy(self->buffer, id);
}

void Shape_init(
    Shape* ptr, 
    void* object,
    void (*delete)(Cloneable*),
    Cloneable* (*clone)(Cloneable*),
    void (*draw)(Shape*)
    ){
  assert(ptr != NULL);
  Cloneable_init(&ptr->base,object,delete, clone);
  ptr->getID = Shape_getID;
  ptr->setID = Shape_setID;
  ptr->draw = draw;
  ptr->buffer[0]=0; //id = ""
}
   
void Shape_destroy(Shape* ptr){
  assert(ptr != NULL);
  Cloneable_destroy(&ptr->base);
  ptr->getID = NULL;
  ptr->setID = NULL;
  ptr->draw = NULL;
  ptr->buffer[0] = 0;
}

void Shape_delete(Cloneable* ptr){
  assert(ptr != NULL);
  Shape *object = (Shape*) ptr->object;
  Shape_destroy(object);
  free(object);
}

Cloneable* Shape_clone(Cloneable* ptr){
  assert(ptr != NULL);
  fprintf(stderr,"Shape::clone is not implemented\n");
  return NULL;
}

void Shape_draw(Shape *self){
  assert(self != NULL);
  fprintf(stderr, "Shape::draw is not implemented\n");
}

Shape* Shape_new(){
  Shape* ptr = (Shape*) malloc (sizeof(Shape));
  Shape_init(ptr, ptr, Shape_delete, Shape_clone, Shape_draw);
  return ptr;
}

void Shape_test(){
  Shape *ptr = Shape_new();
  printf("Shape ID = %s\n",ptr->buffer);
  ptr->setID(ptr,"NewId");
  printf("Shape ID = %s\n",ptr->getID(ptr));
  ptr->base.clone(&ptr->base);
  ptr->draw(ptr);
  Shape_delete(&ptr->base);
}

////////////////////////////////////////////////////////////////////////////////
//                                Rectangle                                   //
////////////////////////////////////////////////////////////////////////////////

typedef struct Rectangle_ Rectangle;
struct Rectangle_ {
  Shape base;
};

void Rectangle_delete(Cloneable*);
Cloneable* Rectangle_clone(Cloneable*);
void Rectangle_draw(Shape*);
void Rectangle_init(Rectangle* ptr){
  assert(ptr != NULL);
  Shape_init(&ptr->base,ptr,Rectangle_delete,Rectangle_clone,Rectangle_draw);
}

void Rectangle_destroy(Rectangle* ptr){
  assert(ptr != NULL);
  Shape_destroy(&ptr->base);

}

void Rectangle_delete(Cloneable* ptr){
  assert(ptr != NULL);
  Rectangle* object = (Rectangle*) ptr->object;
  Rectangle_destroy(object);
  free(object);
}


Rectangle* Rectangle_new(){
  Rectangle* ptr = (Rectangle*) malloc(sizeof(Rectangle));
  Rectangle_init(ptr);
  return ptr;
}

void Rectangle_draw(Shape* self){
  assert(self != NULL);
  printf("Inside Rectangle::draw() method.\n");
}

Cloneable*  Rectangle_clone(Cloneable* ptr){
  assert(ptr != NULL);
  Rectangle* object = (Rectangle*) ptr->object;
  assert(object != NULL);
  Shape* base = &object->base;
  assert(base != NULL);
  char* id = base->getID(base);
  Rectangle* newptr = Rectangle_new();
  assert(newptr != NULL);
  newptr->base.setID(&newptr->base,id);
  Cloneable* clone = &newptr->base.base;
  assert(clone != NULL);
  return clone;
}

void Rectangle_test(){
  Rectangle* ptr = Rectangle_new();
  printf("Rectangle ID: %s\n",ptr->base.getID(&ptr->base));
  ptr->base.setID(&ptr->base,"New Id");
  printf("Rectangle ID: %s\n",ptr->base.getID(&ptr->base));
  Cloneable* clone = ptr->base.base.clone(&ptr->base.base);
  assert(clone != NULL);
  Rectangle* cloned_ptr = (Rectangle*) clone->object;
  assert(cloned_ptr != NULL);
  printf("Rectangle ID: %s\n",cloned_ptr->base.getID(&cloned_ptr->base));
  printf("First Rectangle at address %lx\n", ptr);
  printf("Second Rectangle at address %lx\n", cloned_ptr);
  Rectangle_delete(&ptr->base.base);
  Rectangle_delete(&cloned_ptr->base.base);
}

////////////////////////////////////////////////////////////////////////////////
//                                Square                                      //
////////////////////////////////////////////////////////////////////////////////

typedef struct Square_ Square;
struct Square_ {
  Shape base;
};

void Square_delete(Cloneable*);
Cloneable* Square_clone(Cloneable*);
void Square_draw(Shape*);
void Square_init(Square* ptr){
  assert(ptr != NULL);
  Shape_init(&ptr->base,ptr,Square_delete,Square_clone,Square_draw);
}

void Square_destroy(Square* ptr){
  assert(ptr != NULL);
  Shape_destroy(&ptr->base);

}

void Square_delete(Cloneable* ptr){
  assert(ptr != NULL);
  Square* object = (Square*) ptr->object;
  Square_destroy(object);
  free(object);
}


Square* Square_new(){
  Square* ptr = (Square*) malloc(sizeof(Square));
  Square_init(ptr);
  return ptr;
}

void Square_draw(Shape* self){
  assert(self != NULL);
  printf("Inside Square::draw() method.\n");
}

Cloneable*  Square_clone(Cloneable* ptr){
  assert(ptr != NULL);
  Square* object = (Square*) ptr->object;
  assert(object != NULL);
  Shape* base = &object->base;
  assert(base != NULL);
  char* id = base->getID(base);
  Square* newptr = Square_new();
  assert(newptr != NULL);
  newptr->base.setID(&newptr->base,id);
  Cloneable* clone = &newptr->base.base;
  assert(clone != NULL);
  return clone;
}

void Square_test(){
  Square* ptr = Square_new();
  printf("Square ID: %s\n",ptr->base.getID(&ptr->base));
  ptr->base.setID(&ptr->base,"New Id");
  printf("Square ID: %s\n",ptr->base.getID(&ptr->base));
  Cloneable* clone = ptr->base.base.clone(&ptr->base.base);
  assert(clone != NULL);
  Square* cloned_ptr = (Square*) clone->object;
  assert(cloned_ptr != NULL);
  printf("Square ID: %s\n",cloned_ptr->base.getID(&cloned_ptr->base));
  printf("First Square at address %lx\n", ptr);
  printf("Second Square at address %lx\n", cloned_ptr);
  Square_delete(&ptr->base.base);
  Square_delete(&cloned_ptr->base.base);
}

////////////////////////////////////////////////////////////////////////////////
//                                Circle                                      //
////////////////////////////////////////////////////////////////////////////////

typedef struct Circle_ Circle;
struct Circle_ {
  Shape base;
};

void Circle_delete(Cloneable*);
Cloneable* Circle_clone(Cloneable*);
void Circle_draw(Shape*);
void Circle_init(Circle* ptr){
  assert(ptr != NULL);
  Shape_init(&ptr->base,ptr,Circle_delete,Circle_clone,Circle_draw);
}

void Circle_destroy(Circle* ptr){
  assert(ptr != NULL);
  Shape_destroy(&ptr->base);

}

void Circle_delete(Cloneable* ptr){
  assert(ptr != NULL);
  Circle* object = (Circle*) ptr->object;
  Circle_destroy(object);
  free(object);
}


Circle* Circle_new(){
  Circle* ptr = (Circle*) malloc(sizeof(Circle));
  Circle_init(ptr);
  return ptr;
}

void Circle_draw(Shape* self){
  assert(self != NULL);
  printf("Inside Circle::draw() method.\n");
}

Cloneable*  Circle_clone(Cloneable* ptr){
  assert(ptr != NULL);
  Circle* object = (Circle*) ptr->object;
  assert(object != NULL);
  Shape* base = &object->base;
  assert(base != NULL);
  char* id = base->getID(base);
  Circle* newptr = Circle_new();
  assert(newptr != NULL);
  newptr->base.setID(&newptr->base,id);
  Cloneable* clone = &newptr->base.base;
  assert(clone != NULL);
  return clone;
}

void Circle_test(){
  Circle* ptr = Circle_new();
  printf("Circle ID: %s\n",ptr->base.getID(&ptr->base));
  ptr->base.setID(&ptr->base,"New Id");
  printf("Circle ID: %s\n",ptr->base.getID(&ptr->base));
  Cloneable* clone = ptr->base.base.clone(&ptr->base.base);
  assert(clone != NULL);
  Circle* cloned_ptr = (Circle*) clone->object;
  assert(cloned_ptr != NULL);
  printf("Circle ID: %s\n",cloned_ptr->base.getID(&cloned_ptr->base));
  printf("First Circle at address %lx\n", ptr);
  printf("Second Circle at address %lx\n", cloned_ptr);
  Circle_delete(&ptr->base.base);
  Circle_delete(&cloned_ptr->base.base);
}

////////////////////////////////////////////////////////////////////////////////
//                             PrototypeManager                               //
////////////////////////////////////////////////////////////////////////////////

#define PROTOTYPE_MANAGER_MAX_SIZE 10
typedef struct PrototypeManager_ PrototypeManager;
struct PrototypeManager_ {
  int count;
  Shape* data[PROTOTYPE_MANAGER_MAX_SIZE]; 
};

void PrototypeManager_init(PrototypeManager* ptr){
  assert(ptr != NULL);
  ptr-> count = 0;
  int i;
  for(i = 0; i< PROTOTYPE_MANAGER_MAX_SIZE; ++i){
    ptr->data[i] = NULL;
  }
}

void PrototypeManager_destroy(PrototypeManager* ptr){
  assert(ptr != NULL);
  int i;
  for(i = 0; i <  ptr->count; ++i){
    Cloneable_delete(&ptr->data[i]->base);
  }
  PrototypeManager_init(ptr);
}

void PrototypeManager_loadCache(PrototypeManager* ptr){
  assert(ptr != NULL);
  Rectangle* rect = Rectangle_new();
  rect->base.setID(&rect->base,"1");
  ptr->data[0] = &rect->base;
  Square* square = Square_new();
  square->base.setID(&square->base,"2");
  ptr->data[1] = &square->base;
  Circle* circle = Circle_new();
  circle->base.setID(&circle->base,"3");
  ptr->data[2] = &circle->base;
  ptr->count = 3;
}

Shape* PrototypeManager_getShape(PrototypeManager* ptr, const char* id){
  assert(ptr != NULL);
  int i;
  for(i = 0; i < ptr->count; ++i){
    if(strcmp(ptr->data[i]->getID(ptr->data[i]),id) == 0){
      Shape* found = ptr->data[i];
      assert(found != NULL);
      Cloneable* copy = found->base.clone(&found->base);
      assert(copy != NULL);
      // need to review this inheritance business. Functionality
      // to recover Shape object from concrete object is missing if we
      // do not have knowledge of the concrete type
      Shape* newShape = (Shape*) copy->object;  // cheating here
      return newShape;
    }
  }
  return NULL;
}


int main(int argc, char* argv[]){
  // need a prototype manager
  PrototypeManager manager;
  PrototypeManager_init(&manager);
  // prototype manager registers a few prototypes
  PrototypeManager_loadCache(&manager);
  // prototype manager can now be used as a factory object
  Shape* clonedShape1 = PrototypeManager_getShape(&manager,"1");
  assert(clonedShape1 != NULL);
  clonedShape1->draw(clonedShape1);

  Shape* clonedShape2 = PrototypeManager_getShape(&manager,"2");
  assert(clonedShape2 != NULL);
  clonedShape2->draw(clonedShape2);

  Shape* clonedShape3 = PrototypeManager_getShape(&manager,"3");
  assert(clonedShape3 != NULL);
  clonedShape3->draw(clonedShape3);


  Cloneable_delete(&clonedShape3->base);
  Cloneable_delete(&clonedShape2->base);
  Cloneable_delete(&clonedShape1->base);
  PrototypeManager_destroy(&manager);
  return 0;
}


