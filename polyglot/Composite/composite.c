// Composite Design Pattern
#include <stdio.h>
#include <assert.h>
#include <malloc.h>
#include <string.h>

// The composite design pattern consists in creating an abstract class
// or interface 'Component' which allows client code to handle certain 
// types of primitive objects of type 'Leaf' and various combinations
// thereof in a uniform way. These combinations can be of various nature
// and are unified in a common type 'Composite', where both 'Leaf' and 
// 'Composite' are subclasses of 'Component'.
//
// There are many examples where the composite pattern is applicable
// e.g. the DOM for html and abstract syntax trees for formal languages, 
// inductive data types of Haskell and Coq, etc.
//
// In the SICP course at MIT, a key idea relating to properties of
// programming languages is the existence of 'primitive objects' (Leaf)
// and 'means of combination', allowing the creation of new objects
// (Composite) while remaining within the language. The Composite 
// patterns allows us to regard every language entity as a 'Component' 
// which can be combined with other 'Component'(either 'Leaf' or 
// 'Composite') to obtain a new Component. In Lisp we could say that 
// every Component (which we shall call 'Expression') is either a Leaf 
// (which we shall call 'ExpressionLeaf') or a list of expressions 
// (which we shall call 'ExpressionComposite'). The means of combinations 
// in this case are are simply reduced to gathering objects within lists:
//
// Expression          := ExpressionLeaf | ExpressionComposite
// ExpressionComposite := Nil | Cons Expression ExpressionComposite
//

// data structures representing instances of objects
typedef struct Expression_                Expression;
typedef struct ExpressionLeaf_            ExpressionLeaf;
typedef struct ExpressionComposite_       ExpressionComposite;
typedef struct Primitive_                 Primitive;
typedef struct ExpInt_                    ExpInt;
typedef struct Plus_                      Plus;
typedef struct Mult_                      Mult;
typedef struct Cons_                      Cons;
typedef struct Nil_                       Nil;
typedef struct Environment_               Environment;
typedef struct String_                    String;

// data structures maintaining pointers to virtual methods
typedef struct ExpressionClass_           ExpressionClass;
typedef struct ExpressionLeafClass_       ExpressionLeafClass;
typedef struct ExpressionCompositeClass_  ExpressionCompositeClass;
typedef struct PrimitiveClass_            PrimitiveClass;
typedef struct ExpIntClass_               ExpIntClass;
typedef struct PlusClass_                 PlusClass;
typedef struct MultClass_                 MultClass;
typedef struct ConsClass_                 ConsClass;
typedef struct NilClass_                  NilClass;
typedef struct EnvironmentClass_          EnvironmentClass;

/******************************************************************************/
/*                               String class                                 */
/******************************************************************************/

// attempt at creating a class of immutable strings.
// This coding exercise forbids us to use any C++
struct String_ {
  int count;      // reference count
  int length;
  const char* buffer;
};

String* String_new(const char* from){
  assert(from != NULL);
  int length = strlen(from); // risky, buffer could have no trailing '\0'
  assert(length >= 0);
  char* buffer = (char*) malloc(sizeof(char)*(length + 1));
  assert(buffer != NULL);
  String* obj = (String*) malloc(sizeof(String));
  assert(obj != NULL);
  obj->count = 1;
  obj->length = length;
  obj->buffer = buffer;
  strcpy(buffer,from);
  return obj;
}

String* String_copy(String* self){
  assert(self != NULL);
  assert(self->count > 0);
  assert(self->buffer != NULL);
  self->count++;  // increasing reference count
  return self;
}

void String_delete(String* self){
  assert(self != NULL);
  assert(self->count > 0);
  assert(self->buffer != NULL);
  self->count--;                 // decresing reference count
  if(self->count == 0){
    free((char*)self->buffer);  // casting const away for memory release
    self->buffer = NULL;
    self->length = 0;
    free(self);
  }
}


 


/******************************************************************************/
/*                          Expression class (root)                           */
/******************************************************************************/

struct ExpressionClass_ {
  Expression*   (*eval)     (Expression*, Environment*);
  Expression*   (*apply)    (Expression*, ExpressionComposite*);
  const char*   (*toString) (Expression*);
  int           (*isList)   (Expression*);  // returns 1 if ExpressionComposite 
  int           (*isInt)    (Expression*);  // returns 1 if ExpInt
  void          (*delete)   (Expression*);  // virtual destructor
  int           count;                      // reference counter
};

struct Expression_ {
  int count;                                // reference counter
  ExpressionClass* vTable;
  // no instance data
};


// just boiler-plate, managing vTable indirection
Expression* Expression_eval(Expression *self, Environment* env){
  assert(self != NULL);
  assert(env  != NULL);
  ExpressionClass* vTable = self->vTable;
  assert(vTable != NULL);
  Expression* (*eval)(Expression*, Environment*);
  eval = vTable->eval;
  assert(eval != NULL);
  return eval(self,env);
}

// just boiler-plate, managing vTable indirection
Expression* Expression_apply(Expression *self, ExpressionComposite* args){
  assert(self != NULL);
  assert(args  != NULL);
  ExpressionClass* vTable = self->vTable;
  assert(vTable != NULL);
  Expression* (*apply)(Expression*, ExpressionComposite*);
  apply = vTable->apply;
  assert(apply != NULL);
  return apply(self,args);
}

// just boiler-plate, managing vTable indirection
const char* Expression_toString(Expression *self){
  assert(self != NULL);
  ExpressionClass* vTable = self->vTable;
  assert(vTable != NULL);
  const char* (*toString)(Expression*);
  toString = vTable->toString;
  assert(toString != NULL);
  return toString(self);
}

// just boiler-plate, managing vTable indirection
int Expression_isList(Expression *self){
  assert(self != NULL);
  ExpressionClass* vTable = self->vTable;
  assert(vTable != NULL);
  int (*isList)(Expression*);
  isList = vTable->isList;
  assert(isList != NULL);
  return isList(self);
}

// just boiler-plate, managing vTable indirection
int Expression_isInt(Expression *self){
  assert(self != NULL);
  ExpressionClass* vTable = self->vTable;
  assert(vTable != NULL);
  int (*isInt)(Expression*);
  isInt = vTable->isInt;
  assert(isInt != NULL);
  return isInt(self);
}

/******************************************************************************/
// overload for vTable initialization
int _Expression_isInt(Expression* self){
  return 0;
}
/******************************************************************************/


// just boiler-plate, managing vTable indirection
void Expression_delete(Expression *self){
  assert(self != NULL);
  ExpressionClass* vTable = self->vTable;
  assert(vTable != NULL);
  void (*delete)(Expression*);
  delete = vTable->delete;
  assert(delete != NULL);
  delete(self);
}

/******************************************************************************/
/*                     ExpressionLeaf class (level 1)                         */
/******************************************************************************/

struct ExpressionLeafClass_ {
  // no new virtual methods
};

struct ExpressionLeaf_ {
  Expression base;        // inheritance
};

// just boiler-plate, passing call to base
Expression*  ExpressionLeaf_eval(ExpressionLeaf* self, Environment* env){
  assert(self != NULL);
  assert(env  != NULL);  
  return Expression_eval((Expression*) self, env);    // upcast
}

// just boiler-plate, passing call to base
Expression* ExpressionLeaf_apply(ExpressionLeaf* self, ExpressionComposite* args){
  assert(self != NULL);
  assert(args != NULL);
  return Expression_apply((Expression*) self, args);  // upcast
}

// just boiler-plate, passing call to base
const char* ExpressionLeaf_toString(ExpressionLeaf* self){
  assert(self != NULL);
  return Expression_toString((Expression*) self);     // upcast
}

/******************************************************************************/
// Override
int ExpressionLeaf_isList(ExpressionLeaf* self){
  assert(self != NULL);
  return 0;
}
// overload for vTable initialization
int _ExpressionLeaf_isList(Expression* self){
  assert(self != NULL);
  return ExpressionLeaf_isList((ExpressionLeaf*) self); // downcast
}
/******************************************************************************/

// just boiler-plate, passing call to base
int ExpressionLeaf_isInt(ExpressionLeaf* self){
  assert(self != NULL);
  return Expression_isInt((Expression*) self);
}

// just boiler-plate, passing call to base
void ExpressionLeaf_delete(ExpressionLeaf* self){
  assert(self != NULL);
  Expression_delete((Expression*) self);
}

/******************************************************************************/
/*                    ExpressionComposite class (level 1)                     */
/******************************************************************************/

struct ExpressionCompositeClass_ {
  // new virtual method
  int             (*isNil)  (ExpressionComposite*);
};

struct ExpressionComposite_ {
  Expression base;                    // inheritance
  ExpressionCompositeClass *vTable;   // additional vTable
};

// just boiler-plate, passing call to base
Expression*  ExpressionComposite_eval(ExpressionComposite* self, Environment* env){
  assert(self != NULL);
  assert(env  != NULL);  
  return Expression_eval((Expression*) self, env);    // upcast
}

// just boiler-plate, passing call to base
Expression* ExpressionComposite_apply(
    ExpressionComposite* self, 
    ExpressionComposite* args
){
  assert(self != NULL);
  assert(args != NULL);
  return Expression_apply((Expression*) self, args);  // upcast
}

// just boiler-plate, passing call to base
const char* ExpressionComposite_toString(ExpressionComposite* self){
  assert(self != NULL);
  return Expression_toString((Expression*) self);     // upcast
}

/******************************************************************************/
// Override
int ExpressionComposite_isList(ExpressionComposite* self){
  assert(self != NULL);
  return 1;
}
// overload for vTable initialization
int _ExpressionComposite_isList(Expression* self){
  assert(self != NULL);
  return ExpressionComposite_isList((ExpressionComposite*) self); // downcast
}
/******************************************************************************/

// just boiler-plate, passing call to base
int ExpressionComposite_isInt(ExpressionComposite* self){
  assert(self != NULL);
  return Expression_isInt((Expression*) self);                   // upcast
}

// just boiler-plate, passing call to base
void ExpressionComposite_delete(ExpressionComposite* self){
  assert(self != NULL);
  Expression_delete((Expression*) self);                        // upcast
}

// just boiler-plate, managing vTable indirection
int ExpressionComposite_isNil(ExpressionComposite *self){
  assert(self != NULL);
  ExpressionCompositeClass* vTable = self->vTable;
  assert(vTable != NULL);
  int (*isNil)(ExpressionComposite*);
  isNil = vTable->isNil;
  assert(isNil != NULL);
  return isNil(self);
}

/******************************************************************************/
// This is not a virtual method
void ExpressionComposite_foldLeft(void* init, void* operator, void* result){
  // R* init
  // R* (*operator)(R* arg, Expression* exp)
  // R* result
}

// This is not a virtual method
void ExpressionComposite_foldRight(void* init, void* operator, void* result){
  // R* init
  // R* (*operator)(Expression* exp, R* arg)
  // R* result
}

// This is not a virtual method
ExpressionComposite* ExpressionComposite_evalList(
    ExpressionComposite* self,
    Environment*         env
){

}
/******************************************************************************/


/******************************************************************************/
/*                    ExpressionPrimitive class (level 2)                     */
/******************************************************************************/

struct PrimitiveClass_ {
  // no new virtual method
};

struct Primitive_ {
  ExpressionLeaf base;  // inheritance
};

// just boiler-plate, passing call to base
Expression*  Primitive_eval(Primitive* self, Environment* env){
  assert(self != NULL);
  assert(env  != NULL);  
  return Expression_eval((Expression*) self, env);    // upcast
}

// just boiler-plate, passing call to base
Expression* Primitive_apply(Primitive* self, ExpressionComposite* args){
  assert(self != NULL);
  assert(args != NULL);
  return Expression_apply((Expression*) self, args);  // upcast
}

// just boiler-plate, passing call to base
const char* Primitive_toString(Primitive* self){
  assert(self != NULL);
  return Expression_toString((Expression*) self);     // upcast
}

// just boiler-plate, passing call to base
int Primitive_isList(Primitive* self){
  assert(self != NULL);
  return Expression_isList((Expression*) self);        // upcast
}

// just boiler-plate, passing call to base
int Primitive_isInt(Primitive* self){
  assert(self != NULL);
  return Expression_isInt((Expression*) self);        // upcast
}

// just boiler-plate, passing call to base
void Primitive_delete(Primitive* self){
  assert(self != NULL);
  Expression_delete((Expression*) self);              // upcast
}


/******************************************************************************/
/*                            ExpInt class (level 2)                          */
/******************************************************************************/
struct ExpIntClass_ {
  //  no new virtual function 
};

struct ExpInt_ {
  ExpressionLeaf base;  // inheritance
  int value;            // additional data member
};

ExpInt* ExpInt_copy(ExpInt* self){
  assert(self != NULL);
  Expression* base = (Expression*) self;
  base->count++;
  return self;
}

/******************************************************************************/

// This is not a virtual method
int ExpInt_toInt(ExpInt* self){
  assert(self != NULL);
  return self->value;
}

// Override
Expression*  ExpInt_eval(ExpInt* self, Environment* env){
  assert(self != NULL);
  assert(env  != NULL);  
  ExpInt *copy = ExpInt_copy(self);
  assert(copy != NULL);
  return (Expression*) copy;
}

// overload for vTable initialization
Expression* _ExpInt_eval(Expression* self, Environment* env){
  assert(self != NULL);
  assert(env != NULL);
  return ExpInt_eval((ExpInt*) self, env);               // downcast
}

// Override
Expression* ExpInt_apply(ExpInt* self, ExpressionComposite* args){
  assert(self != NULL);
  assert(args != NULL);
  fprintf(stderr,"An integer is not an operator\n");
  return NULL;
}

// overload for vTable initialization
Expression* _ExpInt_apply(Expression* self, ExpressionComposite* args){
  assert(self != NULL);
  assert(args != NULL);
  return ExpInt_apply((ExpInt*) self, args);             // downcast
}


// Override
// Very sketchy implementation, maintaining single buffer
// This will not work with concurrent access. Not thread safe
// Even with sequential access, caller of
const char* ExpInt_toString(ExpInt* self){

  assert(self != NULL);
  // ------------------------------------------------------------TBI
  return NULL;
}

// overload for vTable initialization
const char* _ExpInt_toString(Expression* self){
  assert(self != NULL);
  return ExpInt_toString((ExpInt*) self);
}


// Override
int ExpInt_isInt(ExpInt* self){
  assert(self != NULL);
  return 1;
}

// overload for vTable initialization
int _ExpInt_isInt(Expression* self){
  assert(self != NULL);
  return ExpInt_isInt((ExpInt*) self);                 // downcast
}

/******************************************************************************/

// just boiler-plate, passing call to base
int ExpInt_isList(ExpInt* self){
  assert(self != NULL);
  return Expression_isList((Expression*) self);        // upcast
}

// just boiler-plate, passing call to base
void ExpInt_delete(ExpInt* self){
  assert(self != NULL);
  Expression_delete((Expression*) self);              // upcast
}



// child of level 2: level 3
struct PlusClass_ {
};

// child of level 2: level 3
struct MultClass_ {
};

// child of level 1: level 2
struct NilClass_ {
};

// child of level 1: level 2
struct ConsClass_ {
};

ExpInt* ExpInt_new(int n){
  return NULL;  // TBI
}

Plus* Plus_new(){
  return NULL;  // TBI
}

Mult* Mult_new(){
  return NULL;  // TBI
}

Nil* Nil_new(){
  return NULL;  // TBI
}

Cons* Cons_new(Expression* car, ExpressionComposite* cdr){
  return NULL;  // TBI
}

int main(int argc, char* argv[], char* envp[]){
  /*
  Expression *two   = (Expression*) ExpInt_new(2);
  Expression *seven = (Expression*) ExpInt_new(7); 
  Expression *five  = (Expression*) ExpInt_new(5); 
  Expression *plus  = (Expression*) Plus_new();
  Expression *mult  = (Expression*) Mult_new(); 
  Expression *exp1  = (Expression*) Cons_new( // (+ 2 7 5)
                                        plus,
                 (ExpressionComposite*) Cons_new(
                                            two,
                     (ExpressionComposite*) Cons_new(
                                                seven,
                         (ExpressionComposite*) Cons_new(
                                                    five,
                             (ExpressionComposite*) Nil_new()))));

  Expression *exp2  = (Expression*) Cons_new( // (* 2 (+ 2 7 5) 5)
                                        mult,
                 (ExpressionComposite*) Cons_new(
                                            two,
                     (ExpressionComposite*) Cons_new(
                                                exp1,
                         (ExpressionComposite*) Cons_new(
                                                    five,
                             (ExpressionComposite*) Nil_new()))));

  printf("The valuation of Lisp expression: %s\n", 
      Expression_toString(exp2)
  );
  printf("yields the value: %s\n", 
      Expression_toString(Expression_eval(exp2, NULL))
  );

  // Need to release memory here: TBI

  */ 
  
  String* x = String_new("Hello World!\n");
  printf("%s",x->buffer);
  String* y = String_copy(x);
  printf("%s",y->buffer);
  String_delete(x);
  String_delete(y);
  return 0;
}

