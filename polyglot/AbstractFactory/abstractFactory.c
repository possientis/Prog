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

void IShape_free(struct IShape Obj){
  free(Obj.object);
  Obj.object = NULL;
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

struct Rectangle {
  struct AbstractShape base;
  // no new member
};

struct Square {
  struct AbstractShape base;
  // no new member
};

struct Circle {
  struct AbstractShape base;
  // no new member
};

// will be needed to initialize function pointer of IShape
void Rectangle_draw(struct IShape* self){
  assert(self != NULL);
  struct Rectangle* pObj = (struct Rectangle*) self->object;
  struct AbstractShape base = pObj->base;
  printf("Drawing %s rectangle\n", base.asString(base.mColor));
}

// will be needed to initialize function pointer of IShape
void Square_draw(struct IShape* self){
  assert(self != NULL);
  struct Square* pObj = (struct Square*) self->object;
  struct AbstractShape base = pObj->base;
  printf("Drawing %s square\n", base.asString(base.mColor));
}

// will be needed to initialize function pointer of IShape
void Circle_draw(struct IShape* self){
  assert(self != NULL);
  struct Circle* pObj = (struct Circle*) self->object;
  struct AbstractShape base = pObj->base;
  printf("Drawing %s circle\n", base.asString(base.mColor));
}

// Initializers
void Rectangle_init(struct Rectangle* pObj, COLOR color){
  assert(pObj != NULL);
  AbstractShape_init(&pObj->base, &Rectangle_draw, pObj,
     &AbstractShape_asString, color);
} 

void Square_init(struct Square* pObj, COLOR color){
  assert(pObj != NULL);
  AbstractShape_init(&pObj->base, &Square_draw, pObj,
     &AbstractShape_asString, color);
} 

void Circle_init(struct Circle* pObj, COLOR color){
  assert(pObj != NULL);
  AbstractShape_init(&pObj->base, &Circle_draw, pObj,
     &AbstractShape_asString, color);
} 

// Constructors
struct Rectangle* Rectangle_new(COLOR color){
  struct Rectangle* ptr = (struct Rectangle*) malloc(sizeof(struct Rectangle));
  Rectangle_init(ptr, color);
  return ptr;
}

struct Square* Square_new(COLOR color){
  struct Square* ptr = (struct Square*) malloc(sizeof(struct Square));
  Square_init(ptr,color);
  return ptr;
}

struct Circle* Circle_new(COLOR color){
  struct Circle* ptr = (struct Circle*) malloc(sizeof(struct Circle));
  Circle_init(ptr,color);
  return ptr;
}

// using the template method pattern here, as the actual
// behaviour of 'getShape' will be defined via specialization
// of virtual method getColor through subclassing
struct AbstractShapeFactory{
  void* object; // pointing to concrete object
  COLOR (*getColor)(); 
  struct IShape (*getShape)(const struct AbstractShapeFactory*, const char*); 
};

// needed to initialize function pointer of AbstractShapeFactory
struct IShape AbstractShapeFactory_getShape(
    const struct AbstractShapeFactory* pObj, const char* shapeType){
  assert(pObj != NULL);
  assert(shapeType != NULL);
  if(shapeType[0] == '\0'){ // testing for empty string
    assert(0);
  }
  if(strcasecmp(shapeType,"CIRCLE") == 0){  // case insensitive comp on POSIX
    return Circle_new(pObj->getColor())->base.base;
  } else if (strcasecmp(shapeType,"RECTANGLE") == 0){
    return Rectangle_new(pObj->getColor())->base.base;
  } else if (strcasecmp(shapeType,"SQUARE") == 0){
    return Square_new(pObj->getColor())->base.base;
  }
  assert(0);
}

void AbstractShapeFactory_init(
    struct AbstractShapeFactory* pObj, void* object, COLOR (*getColor)()){

  assert(pObj != NULL);
  pObj->object = object;
  pObj->getColor = getColor;
  pObj->getShape = AbstractShapeFactory_getShape;

}

void AbstractShapeFactory_free(struct AbstractShapeFactory* pObj){
  assert(pObj != NULL);
  free(pObj->object);
}

// However the benefit of subclassing over maintaining
// 'mColor' state in base class is not that clear in this simple case
// It is propably beneficial when the distinction between various
// families of widgets (IShape) goes well beyond color difference.

struct RedShapeFactory{
  struct AbstractShapeFactory base;
};

struct GreenShapeFactory{
  struct AbstractShapeFactory base;
};

struct BlueShapeFactory{
  struct AbstractShapeFactory base;
};

// needed to initialize function pointer of AbstractShapeFactory 
COLOR getColor_RED(){return RED;}
COLOR getColor_GREEN(){return GREEN;}
COLOR getColor_BLUE(){return BLUE;}


void RedShapeFactory_init(struct RedShapeFactory* pObj){
  assert(pObj != NULL);
  AbstractShapeFactory_init((struct AbstractShapeFactory*)pObj,
      (void*)pObj, getColor_RED);
}

void GreenShapeFactory_init(struct GreenShapeFactory* pObj){
  assert(pObj != NULL);
  AbstractShapeFactory_init((struct AbstractShapeFactory*)pObj,
      (void*)pObj, getColor_GREEN);
}

void BlueShapeFactory_init(struct BlueShapeFactory* pObj){
  assert(pObj != NULL);
  AbstractShapeFactory_init((struct AbstractShapeFactory*)pObj,
      (void*)pObj, getColor_BLUE);
} 

struct RedShapeFactory* RedShapeFactory_new(){
  struct RedShapeFactory* pObj = 
    (struct RedShapeFactory*) malloc(sizeof(struct RedShapeFactory));
  assert(pObj != NULL);
  RedShapeFactory_init(pObj);
  return pObj;
}

struct GreenShapeFactory* GreenShapeFactory_new(){
  struct GreenShapeFactory* pObj = 
    (struct GreenShapeFactory*) malloc(sizeof(struct GreenShapeFactory));
  assert(pObj != NULL);
  GreenShapeFactory_init(pObj);
  return pObj;
}

struct BlueShapeFactory* BlueShapeFactory_new(){
  struct BlueShapeFactory* pObj = 
    (struct BlueShapeFactory*) malloc(sizeof(struct BlueShapeFactory));
  assert(pObj != NULL);
  BlueShapeFactory_init(pObj);
  return pObj;
}

// Factory of factories. The Abstract Factory design pattern is a case
// of Factory design pattern applied to various factory types.
struct FactoryProducer {
  struct AbstractShapeFactory* (*getFactory)(const char*);
};

// needed to initialize function pointer of factory producer
struct AbstractShapeFactory* FactoryProducer_getFactory(const char* factoryType){
  assert(factoryType != NULL);
  if(factoryType[0] == '\0'){ // testing for empty string
    return NULL;
  }
  if(strcasecmp(factoryType,"RED") == 0){  // case insensitive comp on POSIX
    return &RedShapeFactory_new()->base;
  } else if (strcasecmp(factoryType,"GREEN") == 0){
    return &GreenShapeFactory_new()->base;
  } else if (strcasecmp(factoryType,"BLUE") == 0){
    return &BlueShapeFactory_new()->base;
  }
  assert(0);
} 

void FactoryProducer_init(struct FactoryProducer* pObj){
  assert(pObj != NULL);
  pObj->getFactory = &FactoryProducer_getFactory;
}


int main(int arc, char* argv[]){

  struct FactoryProducer producer;
  FactoryProducer_init(&producer);

  // producing set of red widgets
  struct AbstractShapeFactory* redFactory = producer.getFactory("Red");
  assert(redFactory != NULL);
  // getShape method needs a 'this' pointer, or reference to 'self'
  struct IShape shape1 = redFactory->getShape(redFactory,"CIRCLE");
  struct IShape shape2 = redFactory->getShape(redFactory,"RECTANGLE");
  struct IShape shape3 = redFactory->getShape(redFactory,"SQUARE");
  shape1.draw(&shape1);
  shape2.draw(&shape2);
  shape3.draw(&shape3);

  // producing set of green widgets
  struct AbstractShapeFactory* greenFactory = producer.getFactory("Green");
  assert(greenFactory != NULL);
  struct IShape shape4 = greenFactory->getShape(greenFactory,"CIRCLE");
  struct IShape shape5 = greenFactory->getShape(greenFactory,"RECTANGLE");
  struct IShape shape6 = greenFactory->getShape(greenFactory,"SQUARE");
  shape1.draw(&shape4);
  shape2.draw(&shape5);
  shape3.draw(&shape6);
  
  // producing set of blue widgets
  struct AbstractShapeFactory* blueFactory = producer.getFactory("Blue");
  assert(blueFactory != NULL);
  struct IShape shape7 = blueFactory->getShape(blueFactory,"CIRCLE");
  struct IShape shape8 = blueFactory->getShape(blueFactory,"RECTANGLE");
  struct IShape shape9 = blueFactory->getShape(blueFactory,"SQUARE");
  shape1.draw(&shape7);
  shape2.draw(&shape8);
  shape3.draw(&shape9);
 


  // clean up
  IShape_free(shape9);
  IShape_free(shape8);
  IShape_free(shape7);
  IShape_free(shape6);
  IShape_free(shape5);
  IShape_free(shape4);
  IShape_free(shape3);
  IShape_free(shape2);
  IShape_free(shape1);
  AbstractShapeFactory_free(blueFactory);
  AbstractShapeFactory_free(greenFactory);
  AbstractShapeFactory_free(redFactory);

  return 0;
}
