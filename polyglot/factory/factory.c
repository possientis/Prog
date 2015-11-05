#include <stdio.h>
#include <malloc.h>
#include <string.h>
#include <assert.h>

struct IShape {
  void (*draw)();
  void* object; // pointer to concrete object
};

void Rectangle_draw(){
  printf("Inside Rectangle::draw() method.\n");
}

void Square_draw(){
  printf("Inside Square::draw() method.\n");
}

void Circle_draw(){
  printf("Inside Circle::draw() method.\n");
}

struct Rectangle {
  struct IShape base;
  // possibly some concrete data
};

struct Square {
  struct IShape base;
  // possibly some concrete data
};

struct Circle {
  struct IShape base;
  // possibly some concrete data
};



struct Rectangle* getNewRectangle(){
  struct Rectangle* ptr = (struct Rectangle*) malloc(sizeof(struct Rectangle));
  ptr->base.draw = &Rectangle_draw;
  ptr->base.object = (void*) ptr;
  return ptr;
}

struct Square* getNewSquare(){
  struct Square* ptr = (struct Square*) malloc(sizeof(struct Square));
  ptr->base.draw = &Square_draw;
  ptr->base.object = (void*) ptr;
  return ptr;
}

struct Circle* getNewCircle(){
  struct Circle* ptr = (struct Circle*) malloc(sizeof(struct Circle));
  ptr->base.draw = &Circle_draw;
  ptr->base.object = (void*) ptr;
  return ptr;
}

struct IShape ShapeFactory_getShape(const char* shapeType){

  assert(shapeType != NULL);

  if(shapeType[0] == '\0'){ // testing for empty string
    assert(0);
  }

  if(strcasecmp(shapeType,"CIRCLE") == 0){  // case insensitive comp on POSIX
    return getNewCircle()->base;
  } else if (strcasecmp(shapeType,"RECTANGLE") == 0){
    return getNewRectangle()->base;
  } else if (strcasecmp(shapeType,"SQUARE") == 0){
    return getNewSquare()->base;
  }

  assert(0);
}


struct ShapeFactory {
  struct IShape (*getShape)(const char* shapeType);
};

struct ShapeFactory* getNewShapeFactory(){
  struct ShapeFactory* ptr 
    = (struct ShapeFactory*) malloc(sizeof(struct ShapeFactory));
  ptr->getShape = &ShapeFactory_getShape;
  return ptr;
}




int main(int arc, char* argv[]){

  struct ShapeFactory* shapeFactory = getNewShapeFactory();

  // get an object of Circle and call its draw method
  struct IShape shape1 = shapeFactory->getShape("CIRCLE");
  shape1.draw();

  // get an object of Rectangle and call its draw method
  struct IShape shape2 = shapeFactory->getShape("RECTANGLE");
  shape2.draw();

  // get an object of Square and call its draw method
  struct IShape shape3 = shapeFactory->getShape("SQUARE");
  shape3.draw();


  // clean up
  free(shape3.object);
  free(shape2.object);
  free(shape1.object);
  free(shapeFactory);

  return 0;

}
