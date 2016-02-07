// Composite Design Pattern
#include <stdio.h>
#include <assert.h>
#include <malloc.h>

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
/*                            Root class                                      */
/******************************************************************************/

// root class: level 0
struct ExpressionClass_ {
  Expression*   (*eval)     (Expression*, Environment*);
  Expression*   (*apply)    (Expression*, ExpressionComposite*);
  const char*   (*toString) (Expression*);
  int           (*isList)   (Expression*);  // returns 1 if ExpressionComposite 
  int           (*isInt)    (Expression*);  // returns 1 if ExpInt
  void          (*delete)   (Expression*);  // virtual destructor
  int           count;                      // reference counter
};

// root class: level 0
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


// child of root: level 1
struct ExpressionLeafClass_ {
  ExpressionClass baseTable;
  // no new virtual methods
};

// child of root: level 1
struct ExpressionCompositeClass_ {
  ExpressionClass baseTable;
  int             (*isNil)  (ExpressionComposite*);
};

// child of level 1: level 2
struct PrimitiveClass_ {
  ExpressionLeafClass baseTable;
  // no new virtual method
};

// child of level 1: level 2
struct ExpIntClass_ {
  ExpressionLeafClass baseTable;
};

// child of level 2: level 3
struct PlusClass_ {
  PrimitiveClass baseTable;
};

// child of level 2: level 3
struct MultClass_ {
  PrimitiveClass baseTable;
};

// child of level 1: level 2
struct NilClass_ {
  ExpressionCompositeClass baseTable;
};

// child of level 1: level 2
struct ConsClass_ {
  ExpressionCompositeClass baseTable;
};

// level 1
struct ExpressionLeaf_ {
  Expression base;        // inheritance
};

// level 1
struct ExpressionComposite_ {
  Expression base;        // inheritance
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

  return 0;
}

