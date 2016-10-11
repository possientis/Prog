// the Abstract Factory pattern looks like the factory pattern 
// applied to the production of various factories
#include <stdio.h>
#include <malloc.h>
#include <string.h>
#include <assert.h>

struct IShape {
  void* object;                       // pointer to concrete object
  void (*draw)(struct IShape* self);  // need to pass a 'this' pointer
};

void IShape_init(struct IShape* pObj, void (*draw)(struct IShape*), void* object){
  assert(pObj != NULL);
  pObj->draw = draw;
  pObj->object = object;
}

void IShape_free(struct IShape* pObj){
  assert(pObj != NULL);
  free(pObj->object);
  pObj->object = NULL;
}

typedef enum {RED, GREEN, BLUE} COLOR;

struct AbstractShape {
  struct IShape base;                   // inheritance
  COLOR mColor;                         // new data member
};

// would be a static member in C++ for name encapsulation
// not much point adding function pointer to a struct in C
// as it would require initialization with something anyway  
static const char* asString(COLOR color){
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

void AbstractShape_init(struct AbstractShape* pObj, void (*draw)(struct IShape*),
   void* object, COLOR color){
  assert(pObj != NULL);
  // base initialization
  IShape_init(&pObj->base,draw,object);
  // new members initialization
  pObj->mColor = color;
} 

struct Rectangle {
  struct AbstractShape base;  // inheritance
  // no new member
};

struct Square {
  struct AbstractShape base;  // inheritance
  // no new member
};

struct Circle {
  struct AbstractShape base;  // inheritance
  // no new member
};

// will be needed to initialize function pointer of IShape
void Rectangle_draw(struct IShape* self){ // 'self' is 'this' pointer
  assert(self != NULL);
  struct Rectangle* pObj = (struct Rectangle*) self->object;
  struct AbstractShape base = pObj->base;
  printf("Drawing %s rectangle\n", asString(base.mColor));
}

// will be needed to initialize function pointer of IShape
void Square_draw(struct IShape* self){
  assert(self != NULL);
  struct Square* pObj = (struct Square*) self->object;
  struct AbstractShape base = pObj->base;
  printf("Drawing %s square\n", asString(base.mColor));
}

// will be needed to initialize function pointer of IShape
void Circle_draw(struct IShape* self){
  assert(self != NULL);
  struct Circle* pObj = (struct Circle*) self->object;
  struct AbstractShape base = pObj->base;
  printf("Drawing %s circle\n", asString(base.mColor));
}

// Initializers
void Rectangle_init(struct Rectangle* pObj, COLOR color){
  assert(pObj != NULL);
  AbstractShape_init(&pObj->base, &Rectangle_draw, (void*) pObj, color);
} 

void Square_init(struct Square* pObj, COLOR color){
  assert(pObj != NULL);
  AbstractShape_init(&pObj->base, &Square_draw, (void*) pObj, color);
} 

void Circle_init(struct Circle* pObj, COLOR color){
  assert(pObj != NULL);
  AbstractShape_init(&pObj->base, &Circle_draw, (void*) pObj, color);
} 

// Constructors
struct Rectangle* Rectangle_new(COLOR color){
  struct Rectangle* pObj = (struct Rectangle*) malloc(sizeof(struct Rectangle));
  Rectangle_init(pObj, color);
  return pObj;
}

struct Square* Square_new(COLOR color){
  struct Square* pObj = (struct Square*) malloc(sizeof(struct Square));
  Square_init(pObj,color);
  return pObj;
}

struct Circle* Circle_new(COLOR color){
  struct Circle* pObj = (struct Circle*) malloc(sizeof(struct Circle));
  Circle_init(pObj,color);
  return pObj;
}

// using the template method pattern here, as the actual
// behaviour of 'getShape' will be defined via specialization
// of virtual method getColor through subclassing
struct AbstractShapeFactory{
  void* object;                 // pointing to concrete object
  COLOR (*getColor)();          // pure virtual; simple enough no need for 'this'
  struct IShape* (*getShape)(const struct AbstractShapeFactory*, const char*); 
};

// needed to initialize function pointer of AbstractShapeFactory
struct IShape* AbstractShapeFactory_getShape( // need a 'this' pointer -> 'self'
    const struct AbstractShapeFactory* self, const char* shapeType){
  assert(self != NULL);
  assert(shapeType != NULL);
  if(shapeType[0] == '\0'){                 // testing for empty string
    return NULL;
  }
  if(strcasecmp(shapeType,"CIRCLE") == 0){  // case insensitive comp on POSIX
    return &Circle_new(self->getColor())->base.base;
  } else if (strcasecmp(shapeType,"RECTANGLE") == 0){
    return &Rectangle_new(self->getColor())->base.base;
  } else if (strcasecmp(shapeType,"SQUARE") == 0){
    return &Square_new(self->getColor())->base.base;
  }
  assert(0);
}

void AbstractShapeFactory_init(
    struct AbstractShapeFactory* pObj, void* object, COLOR (*getColor)()){
  assert(pObj != NULL);
  pObj->object = object;
  pObj->getColor = getColor;                      // pure virtual
  pObj->getShape = AbstractShapeFactory_getShape; // not virtual

}

void AbstractShapeFactory_free(struct AbstractShapeFactory* pObj){
  assert(pObj != NULL);
  free(pObj->object);
  pObj->object = NULL;
}

// However the benefit of subclassing over maintaining
// 'mColor' state in base class is not that clear in this simple case
// It is propably beneficial when the distinction between various
// families of widgets (IShape) goes well beyond color difference.

struct RedShapeFactory{
  struct AbstractShapeFactory base; // inheritance
};

struct GreenShapeFactory{
  struct AbstractShapeFactory base; // inheritance
};

struct BlueShapeFactory{
  struct AbstractShapeFactory base; // inheritance
};

// needed to initialize function pointer of AbstractShapeFactory 
COLOR getColor_RED(){return RED;}
COLOR getColor_GREEN(){return GREEN;}
COLOR getColor_BLUE(){return BLUE;}


void RedShapeFactory_init(struct RedShapeFactory* pObj){
  assert(pObj != NULL);
  AbstractShapeFactory_init(&pObj->base, (void*)pObj, getColor_RED);
}

void GreenShapeFactory_init(struct GreenShapeFactory* pObj){
  assert(pObj != NULL);
  AbstractShapeFactory_init(&pObj->base, (void*)pObj, getColor_GREEN);
}

void BlueShapeFactory_init(struct BlueShapeFactory* pObj){
  assert(pObj != NULL);
  AbstractShapeFactory_init(&pObj->base, (void*)pObj, getColor_BLUE);
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
  struct AbstractShapeFactory* (*getFactory)(const char*); // no need for 'this'
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


// trying to make the code look better
typedef struct AbstractShapeFactory* pShapeFactory;
typedef struct IShape* pShape;

int main(int arc, char* argv[]){

  struct FactoryProducer producer; FactoryProducer_init(&producer);
  // producing set of red widgets
  pShapeFactory redFactory = producer.getFactory("Red");
  pShape shape1 = redFactory->getShape(redFactory,"CIRCLE");
  pShape shape2 = redFactory->getShape(redFactory,"RECTANGLE");
  pShape shape3 = redFactory->getShape(redFactory,"SQUARE");
  shape1->draw(shape1);
  shape2->draw(shape2);
  shape3->draw(shape3);

  // producing set of green widgets
  pShapeFactory greenFactory = producer.getFactory("Green");
  pShape shape4 = greenFactory->getShape(greenFactory,"CIRCLE");
  pShape shape5 = greenFactory->getShape(greenFactory,"RECTANGLE");
  pShape shape6 = greenFactory->getShape(greenFactory,"SQUARE");
  shape1->draw(shape4);
  shape2->draw(shape5);
  shape3->draw(shape6);
  
  // producing set of blue widgets
  pShapeFactory blueFactory = producer.getFactory("Blue");
  pShape shape7 = blueFactory->getShape(blueFactory,"CIRCLE");
  pShape shape8 = blueFactory->getShape(blueFactory,"RECTANGLE");
  pShape shape9 = blueFactory->getShape(blueFactory,"SQUARE");
  shape1->draw(shape7);
  shape2->draw(shape8);
  shape3->draw(shape9);

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
