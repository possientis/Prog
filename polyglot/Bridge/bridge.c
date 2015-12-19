// Bridge design pattern
#include <malloc.h>
#include <stdio.h>
#include <assert.h>

// bridge implementation interface
typedef struct DrawAPI_ DrawAPI;
struct DrawAPI_ {
  void (*delete)(DrawAPI*); // virtual destructor
  void (*drawCircle)(DrawAPI*, int, int, int);
};

void DrawAPI_init(
    DrawAPI* self, void (*delete)(DrawAPI*), 
    void (*drawCircle)(DrawAPI*, int, int, int)
    ){
  assert(self != NULL);
  assert(delete != NULL);
  assert(drawCircle != NULL);
  self->delete = delete;
  self->drawCircle = drawCircle;
}

void DrawAPI_destroy(DrawAPI * self){
  assert(self != NULL);
  self->delete = NULL;
  self->drawCircle = NULL;
}

// virtual
void DrawAPI_delete(DrawAPI *self){
  assert(self != NULL);
  void (*delete)(DrawAPI*);
  delete = self->delete;
  assert(delete != NULL);
  delete(self);
}

// virtual
void DrawAPI_drawCircle(DrawAPI* self, int radius, int x, int y){
  assert(self != NULL);
  assert(self->drawCircle != NULL);
  self->drawCircle(self, radius, x, y);
}


// concrete bridge implementation classes implementing DrawAPI interface
typedef struct RedCircle_ RedCircle;
struct RedCircle_ {
  DrawAPI _drawAPI;  // base object
};

void RedCircle_delete(DrawAPI*);                    // forward declaration
void RedCircle_drawCircle(DrawAPI*, int, int, int); // forward declaration
void RedCircle_init(RedCircle* self){
  assert(self != NULL);
  DrawAPI_init(&self->_drawAPI, RedCircle_delete, RedCircle_drawCircle);
}

RedCircle *RedCircle_new(){
  RedCircle* ptr = (RedCircle*) malloc(sizeof(RedCircle));
  assert(ptr != NULL);
  RedCircle_init(ptr);
  return ptr;
}

void RedCircle_destroy(RedCircle* self){
  assert(self != NULL);
  DrawAPI_destroy(&self->_drawAPI);
}

// override
void RedCircle_delete(DrawAPI* self){
  assert(self != NULL);
  RedCircle* object = (RedCircle*) self;
  RedCircle_destroy(object);
  free(object);
}

// override
void RedCircle_drawCircle(DrawAPI* self, int radius, int x, int y){
  assert(self != NULL); // not using object specifics anyway
  printf("Drawing Circle[ color: red  , radius: %d, x: %d, y: %d]\n",radius,x,y);
}

typedef struct GreenCircle_ GreenCircle;
struct GreenCircle_ {
  DrawAPI _drawAPI;  // base object
};

void GreenCircle_delete(DrawAPI*);                    // forward declaration
void GreenCircle_drawCircle(DrawAPI*, int, int, int); // forward declaration
void GreenCircle_init(GreenCircle* self){
  assert(self != NULL);
  DrawAPI_init(&self->_drawAPI, GreenCircle_delete, GreenCircle_drawCircle);
}

GreenCircle *GreenCircle_new(){
  GreenCircle* ptr = (GreenCircle*) malloc(sizeof(GreenCircle));
  assert(ptr != NULL);
  GreenCircle_init(ptr);
  return ptr;
}

void GreenCircle_destroy(GreenCircle* self){
  assert(self != NULL);
  DrawAPI_destroy(&self->_drawAPI);
}

// override
void GreenCircle_delete(DrawAPI* self){
  assert(self != NULL);
  GreenCircle* object = (GreenCircle*) self;
  GreenCircle_destroy(object);
  free(object);
}

// override
void GreenCircle_drawCircle(DrawAPI* self, int radius, int x, int y){
  assert(self != NULL); // not using object specifics anyway
  printf("Drawing Circle[ color: green, radius: %d, x: %d, y: %d]\n",radius,x,y);
}


// create an abstract class Shape using the DrawAPI interface.
typedef struct Shape_ Shape;
struct Shape_ {
  DrawAPI* _drawAPI;      // Shape has ownership of this pointer
  void (*delete)(Shape*); // virtual destructor
  void (*draw)(Shape*);   // virtual
};

void Shape_init(
    Shape* self, DrawAPI* drawAPI, void (*delete)(Shape*), void(*draw)(Shape*)){
  assert(self != NULL);
  assert(drawAPI != NULL);
  assert(delete != NULL);
  assert(draw != NULL);
  self->_drawAPI = drawAPI;
  self->delete = delete;
  self->draw = draw;
}

void Shape_destroy(Shape* self){
  assert(self != NULL);
  DrawAPI_delete(self->_drawAPI);
  self->_drawAPI = NULL;
  self->delete = NULL;
  self->draw = NULL;
}

void Circle_delete(Shape* self);
// virtual
void Shape_delete(Shape* self){
  assert(self != NULL);
  void (*delete)(Shape*);
  assert(self->delete != NULL);
  assert(self->delete == Circle_delete);
  delete = self->delete;
  assert(delete != NULL);
  delete(self);
}

// virtual
void Shape_draw(Shape* self){
  assert(self != NULL);
  assert(self->draw != NULL);
  self->draw(self);
}

// create concrete class implementing the Shape interface (abstract class)
typedef struct Circle_ Circle;
struct Circle_ {
  Shape _shape; // base object
  int _x;
  int _y;
  int _radius;
};

void Circle_delete(Shape*); // forward declaration
void Circle_draw(Shape*);   // forward declaration
void Circle_init(Circle* self, int x, int y, int radius, DrawAPI* drawAPI){
  assert(self != NULL);
  assert(drawAPI != NULL);
  Shape_init(&self->_shape, drawAPI, Circle_delete, Circle_draw);
  self->_x = x;
  self->_y = y;
  self->_radius = radius;
  assert(self->_shape._drawAPI == drawAPI);
  assert(self->_shape.delete == Circle_delete);
  assert(self->_shape.draw == Circle_draw);
}

Circle* Circle_new(int x, int y, int radius, DrawAPI* drawAPI){
  assert(drawAPI != NULL);
  Circle *ptr = (Circle*) malloc(sizeof(Circle));
  assert(ptr != NULL);
  Circle_init(ptr, x, y, radius, drawAPI);
  assert(ptr->_x == x);
  assert(ptr->_y == y);
  assert(ptr->_radius == radius);
  assert(ptr->_shape._drawAPI  == drawAPI);
  return ptr;
}

void Circle_destroy(Circle* self){
  assert(self != NULL);
  Shape_destroy(&self->_shape);
  self->_x = 0;
  self->_y = 0;
  self->_radius = 0;
}

// override
void Circle_delete(Shape* self){
  assert(self != NULL);
  Circle* object = (Circle*) self;  // concrete object from base
  Circle_destroy(object);
  free(object);
}

// override
void Circle_draw(Shape* self){
  assert(self != NULL);
  Circle* object = (Circle*) self;  // concrete object from base
  DrawAPI* drawAPI = self->_drawAPI;
  assert(drawAPI != NULL);
  DrawAPI_drawCircle(drawAPI, object->_radius, object->_x, object->_y); 
}

// Use Shape and DrawAPI classes to draw different colored circles
int main(int argc, char* argv[], char* envp[]){
  // creating two seperate implementation objects
  DrawAPI* redAPI = (DrawAPI*) RedCircle_new();
  DrawAPI* greenAPI = (DrawAPI*) GreenCircle_new();
  // implementation of concrete circles selected at run time.
  Shape* redCircle = (Shape*) Circle_new(100, 100, 10, redAPI);
  Shape* greenCircle = (Shape*) Circle_new(100, 100, 10, greenAPI);
  Shape_draw(redCircle);
  Shape_draw(greenCircle);
  // Clean necessary in C
  Shape_delete(redCircle);
  Shape_delete(greenCircle);
  return 0;
}
