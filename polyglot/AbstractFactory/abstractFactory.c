// the Abstract Factory pattern looks like the factory pattern 
// applied to the production of various factories
#include <stdio.h>
#include <malloc.h>
#include <string.h>
#include <assert.h>

struct IShape {
  void (*draw)(struct IShape* self);
  void* object; // pointer to concrete object
};

void IShape_init(struct IShape* pObj, void (*draw)(struct IShape*), void* object){
  assert(pObj != NULL);
  pObj->draw = draw;
  pObj->object = object;
}

typedef enum {RED, GREEN, BLUE} COLOR;

struct AbstractShape {
  struct IShape base;
  const char* (*asString)(COLOR color);
  COLOR mColor;
};

void AbstractShape_init(struct AbstractShape* pObj, void (*draw)(struct IShape*),
   void* object, const char* (*asString)(COLOR), COLOR color){
  assert(pObj != NULL);
  // base initialization
  IShape_init(&pObj->base,draw,object);
  // new members initialization
  pObj-> asString = asString;
  pObj->mColor = color;
} 

const char* AbstractShape_asString(COLOR color){
  switch(color){
    case RED:
      return "red";
    case GREEN:
      return "green";
    case BLUE:
      return "blue";
    default:
      return "unknown color";
  }
}

void Rectangle_draw(struct IShape* self){
  printf("Inside Rectangle::draw() method.\n");
}

void Square_draw(struct IShape* self){
  printf("Inside Square::draw() method.\n");
}

void Circle_draw(struct IShape* self){
  printf("Inside Circle::draw() method.\n");
}


struct Rectangle {
  struct AbstractShape base;
  // no new member
};

void Rectangle_init(struct Rectangle* pObj, COLOR color){
  assert(pObj != NULL);
  AbstractShape_init(&pObj->base, &Rectangle_draw, pObj,
     &AbstractShape_asString, color);
} 


struct Square {
  struct AbstractShape base;
  // no new member
};

void Square_init(struct Square* pObj, COLOR color){
  assert(pObj != NULL);
  AbstractShape_init(&pObj->base, &Square_draw, pObj,
     &AbstractShape_asString, color);
} 


struct Circle {
  struct AbstractShape base;
  // no new member
};

void Circle_init(struct Circle* pObj, COLOR color){
  assert(pObj != NULL);
  AbstractShape_init(&pObj->base, &Circle_draw, pObj,
     &AbstractShape_asString, color);
} 


struct Rectangle* getNewRectangle(COLOR color){
  struct Rectangle* ptr = (struct Rectangle*) malloc(sizeof(struct Rectangle));
  Rectangle_init(ptr, color);
  return ptr;
}

struct Square* getNewSquare(COLOR color){
  struct Square* ptr = (struct Square*) malloc(sizeof(struct Square));
  Square_init(ptr,color);
  return ptr;
}

struct Circle* getNewCircle(COLOR color){
  struct Circle* ptr = (struct Circle*) malloc(sizeof(struct Circle));
  Circle_init(ptr,color);
  return ptr;
}


struct IShape ShapeFactory_getShape(const char* shapeType){

  assert(shapeType != NULL);
  if(shapeType[0] == '\0'){ // testing for empty string
    assert(0);
  }

  if(strcasecmp(shapeType,"CIRCLE") == 0){  // case insensitive comp on POSIX
    return getNewCircle(RED)->base.base;
  } else if (strcasecmp(shapeType,"RECTANGLE") == 0){
    return getNewRectangle(RED)->base.base;
  } else if (strcasecmp(shapeType,"SQUARE") == 0){
    return getNewSquare(RED)->base.base;
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
  shape1.draw(&shape1);

  // get an object of Rectangle and call its draw method
  struct IShape shape2 = shapeFactory->getShape("RECTANGLE");
  shape2.draw(&shape2);

  // get an object of Square and call its draw method
  struct IShape shape3 = shapeFactory->getShape("SQUARE");
  shape3.draw(&shape3);


  // clean up
  free(shape3.object);
  free(shape2.object);
  free(shape1.object);
  free(shapeFactory);

  return 0;
}
