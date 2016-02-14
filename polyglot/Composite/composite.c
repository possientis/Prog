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

// rough visual check of memory allocation vs release to avoid leaks
void memory_log(const char* message, const void* ptr){
  fprintf(stderr,message,ptr); // message should have '%lx' referring to ptr
}


/******************************************************************************/
/*                            Environment class                               */
/******************************************************************************/

struct Environment_ {
  int count;
};

Environment* Environment_new(){
  Environment* obj = (Environment*) malloc(sizeof(Environment));
  assert(obj != NULL);
  return obj;
}

void Environment_delete(Environment* self){
  assert(self != NULL);
  free(self);
}

/******************************************************************************/
/*                               String class                                 */
/******************************************************************************/

// attempt at creating a class of immutable strings. C++ is not allowed here
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
  memory_log("allocating string buffer %lx\n", buffer);
  assert(buffer != NULL);
  String* obj = (String*) malloc(sizeof(String));
  memory_log("allocating string object %lx\n", obj);
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
  memory_log("making copy of string object %lx\n", self);
  self->count++;  // increasing reference count
  return self;
}

void String_delete(String* self){
  assert(self != NULL);
  assert(self->count > 0);
  assert(self->buffer != NULL);
  self->count--;                 // decresing reference count
  if(self->count == 0){
    memory_log("deallocating string buffer %lx\n", self->buffer);
    free((char*)self->buffer);  // casting const away for memory release
    self->buffer = NULL;
    self->length = 0;
    memory_log("deallocating string object %lx\n", self);
    free(self);
  }
  else{
    memory_log("deleting copy of string object %lx\n",self);
  }
}

// takes ownership of both strings, which do not need deallocation by caller
String *String_append(String* str1, String* str2){
  assert(str1 != NULL);
  assert(str2 != NULL);
  int len1 = str1->length;
  int len2 = str2->length;
  int len = len1 + len2;
  char* buffer = (char*) malloc(sizeof(char) * (len + 1));
  assert(buffer != NULL);
  memory_log("allocating string buffer %lx for append operation\n", buffer);
  strcpy(buffer, str1->buffer);
  strcat(buffer, str2->buffer);
  String* obj = (String*) malloc(sizeof(String)); 
  memory_log("allocating string object %lx for append operation\n", obj);
  assert(obj != NULL);
  obj->count = 1;
  obj->length = len;
  obj->buffer = buffer;
  String_delete(str1);
  String_delete(str2);
  return obj; 
}

/******************************************************************************/
/*                          Expression class (root)                           */
/******************************************************************************/

struct ExpressionClass_ {
  Expression*   (*eval)     (Expression*, Environment*);
  Expression*   (*apply)    (Expression*, ExpressionComposite*);
  String*       (*toString) (Expression*);
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

Expression* Expression_copy(Expression* self){
  assert(self != NULL);
  assert(self->count > 0);
  memory_log("making copy of Expression object %lx\n", self);
  self->count++;
  return self;
}

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
String* Expression_toString(Expression *self){
  assert(self != NULL);
  ExpressionClass* vTable = self->vTable;
  assert(vTable != NULL);
  String* (*toString)(Expression*);
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
String* ExpressionLeaf_toString(ExpressionLeaf* self){
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
  int (*isNil)  (ExpressionComposite*);
  int count;
};

struct ExpressionComposite_ {
  Expression base;                    // inheritance
  ExpressionCompositeClass *vTable;   // additional vTable
};

ExpressionComposite* ExpressionComposite_copy(ExpressionComposite* self){
  assert(self != NULL);
  Expression* base = (Expression*) self;
  assert(base->count >0);
  memory_log("making copy of ExpressionComposite object %lx\n", self);
  base->count++;
  return self;
}

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
String* ExpressionComposite_toString(ExpressionComposite* self){
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
Expression* Cons_head(Cons*);          // forward
ExpressionComposite* Cons_tail(Cons*); // forward
void Cons_delete(Cons*);               // forward

void* ExpressionComposite_foldLeft(ExpressionComposite* self,
    void* init, void* (*operator)(void*, void*, void* params), void* params){
    // Let R be a type, the type interpretation of arguments is as follows:
    // R* init
    // R* (*operator)(R* arg, Expression* exp, void* params)
    // foldLeft returns a pointer to R.
    assert(init != NULL);
    assert(operator != NULL);
    void *out = init;
    // does not take ownership of self. Caller still needs to deallocate
    // its reference to self. Hence, we are taking copy here to increase
    // reference count.
    ExpressionComposite* next = ExpressionComposite_copy(self);
    while(!ExpressionComposite_isNil(next)){
      assert(!ExpressionComposite_isNil(next));
      Cons* cell = (Cons*) next;        // safe in view of assert
      // this returns a copy, which will require deallocation
      Expression* head = Cons_head(cell);
      out = operator(out, head, params);// key line
      Expression_delete(head);          // deallocation of copy
      next = Cons_tail(cell);           // also returns a copy
      Cons_delete(cell);                // deallocation of cell (previous next)
    }
    ExpressionComposite_delete(next);
    return out;
}

// This is not a virtual method
void* ExpressionComposite_foldRight(ExpressionComposite* self,
    void* init, void* (*operator)(void*, void*, void* params), void* params){
    // Let R be a type, the type interpretation of arguments is as follows:
    // R* init
    // R* (*operator)(Expression* exp, R* arg, void* params)
    // foldRight returns a pointer to R.
    assert(init != NULL);
    assert(operator != NULL);
    if(ExpressionComposite_isNil(self)) return init;
    assert(!ExpressionComposite_isNil(self));
    Cons* cell = (Cons*) self;                    // safe in view of assert
    Expression* head = Cons_head(cell);           // returns a copy
    ExpressionComposite* tail = Cons_tail(cell);  // also a copy
    // recursive call
    void* result = ExpressionComposite_foldRight(tail,init,operator, params);
    result = operator(head, result, params);
    Expression_delete(head);                      // deallocation of copy
    ExpressionComposite_delete(tail);             // deallocation of copy
    return result; 
}

Cons* Cons_new(Expression*, ExpressionComposite*);// forward
void* Operator_evalList(void* exp, void* list, void* params){
  assert(exp != NULL);
  assert(list != NULL);
  assert(params != NULL);

  // casting argument into their expected types
  Expression* expression         = (Expression*) exp;
  ExpressionComposite* evaluated = (ExpressionComposite*) list;
  Environment* env               = (Environment*) params;


  Expression* value = Expression_eval(expression,env);
  Cons* cons = Cons_new(value,evaluated); // cons takes ownership of value, list
  // caller keeps ownership of exp
  // caller takes ownership of new cons, but loses that of list
  return cons;
}

Nil* Nil_new(); // forward
// This is not a virtual method
ExpressionComposite* ExpressionComposite_evalList(
    ExpressionComposite* self,
    Environment*         env
){
  assert(self != NULL);
  assert(env != NULL);
  Expression* nil = (Expression*) Nil_new();
  return ExpressionComposite_foldRight(self, nil, Operator_evalList, env); 
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
String* Primitive_toString(Primitive* self){
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

/******************************************************************************/
// This is not a virtual method
int ExpInt_toInt(ExpInt* self){
  assert(self != NULL);
  return self->value;
}
/******************************************************************************/


ExpressionClass* ExpInt_vTable_copy(ExpressionClass* self){
  assert(self != NULL);
  memory_log("making copy of ExpInt vTable %lx\n", self);
  self->count++;
  return self;
}

ExpInt* ExpInt_copy(ExpInt* self){
  assert(self != NULL);
  memory_log("making copy of ExpInt object %lx\n",self);
  Expression* base = (Expression*) self;
  base->count++;
  return self;
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
  fprintf(stderr,"ExpInt_apply: An integer is not an operator\n");
  return NULL;
}

// overload for vTable initialization
Expression* _ExpInt_apply(Expression* self, ExpressionComposite* args){
  assert(self != NULL);
  assert(args != NULL);
  return ExpInt_apply((ExpInt*) self, args);             // downcast
}


// Override
String* ExpInt_toString(ExpInt* self){
  assert(self != NULL);
  char temp[24];  // on stack, not static, so should be thread safe
  sprintf(temp,"%d",ExpInt_toInt(self));
  String* str = String_new(temp);
  return str; // caller has ownership of String. not returning copy
}

// overload for vTable initialization
String* _ExpInt_toString(Expression* self){
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

// just boiler-plate, passing call to base
int ExpInt_isList(ExpInt* self){
  assert(self != NULL);
  return Expression_isList((Expression*) self);        // upcast
}



void ExpInt_vTable_delete(ExpressionClass*);          // forward

// Override
void ExpInt_delete(ExpInt* self){
  assert(self != NULL);
  Expression* base = (Expression*) self;  //upcast
  assert(base->count > 0);
  base->count--;
  if(base->count == 0){
    assert(base->vTable != NULL);
    ExpInt_vTable_delete(base->vTable);
    self->value = 0;
    memory_log("deallocating ExpInt object %lx\n", self);
    free(self);
  } else{
    memory_log("deleting copy of ExpInt %lx\n", self);
  }
}

// overload for vTable initialization
void _ExpInt_delete(Expression* self){
  assert(self != NULL);
  ExpInt_delete((ExpInt*) self);               // downcast
}
// if vTable gets deallocated by destructor, it needs to communicate that
// fact to this function, so it can discard its dangling referrence 'instance'
// Hence the boolean (int) argument.

ExpressionClass* ExpInt_vTable_new(int killInstance){

  static ExpressionClass* instance = NULL;  // only one instance for ExpInt
  
  if(killInstance){
    instance = NULL;
    return NULL;
  }

  if(instance != NULL) return ExpInt_vTable_copy(instance);

  // real memory allocation
  instance = (ExpressionClass*) malloc(sizeof(ExpressionClass));
  assert(instance != NULL);
  memory_log("allocating ExpInt vTable %lx\n", instance);
  instance->count     = 1;  // first reference
  instance->eval      = _ExpInt_eval;
  instance->apply     = _ExpInt_apply;
  instance->toString  = _ExpInt_toString;
  instance->isList    = _ExpressionLeaf_isList;
  instance->isInt     = _ExpInt_isInt;
  instance->delete    = _ExpInt_delete;
  return instance;
}

void ExpInt_vTable_delete(ExpressionClass* self){
  assert(self != NULL);
  assert(self->count >0);
  self->count--;
  if(self->count == 0){
  memory_log("deallocating ExpInt vTable %lx\n", self);
  self->eval      = NULL;
  self->apply     = NULL;
  self->toString  = NULL;
  self->isList    = NULL;
  self->isInt     = NULL;
  self->delete    = NULL;
  free(self);
  ExpInt_vTable_new(1); // setting static 'instance' of singleton to NULL
  }
  else{
    memory_log("deleting copy of ExpInt vTable %lx\n", self);
  }
}

ExpInt* ExpInt_new(int value){
  ExpInt* obj = (ExpInt*) malloc(sizeof(ExpInt));
  assert(obj != NULL);
  memory_log("allocating ExpInt object %lx\n",obj);
  obj->value = value;
  ExpressionLeaf* leaf = (ExpressionLeaf*) obj; //upcast
  // nothing need setting up for ExpressionLeaf, going further up the chain
  Expression* base = (Expression *) obj;        // upcast
  base->count = 1;                              // first reference
  base->vTable = ExpInt_vTable_new(0);          // '0' indicates normal use 
  assert(base->vTable != NULL);
  return obj;
}

/******************************************************************************/
/*                            Plus class (level 3)                            */
/******************************************************************************/

struct PlusClass_ {
};

struct Plus_ {
  Primitive base;
};

ExpressionClass* Plus_vTable_copy(ExpressionClass* self){
  assert(self != NULL);
  memory_log("making copy of Plus vTable %lx\n", self);
  self->count++;
  return self;
}

Plus* Plus_copy(Plus* self){
  assert(self != NULL);
  memory_log("making copy of Plus object %lx\n", self);
  Expression* base = (Expression*) self;
  base->count++;
  return self;
}

// Override
Expression*  Plus_eval(Plus* self, Environment* env){
  assert(self != NULL);
  assert(env  != NULL);  
  Plus *copy = Plus_copy(self);
  assert(copy != NULL);
  return (Expression*) copy;
}

// overload for vTable initialization
Expression* _Plus_eval(Expression* self, Environment* env){
  assert(self != NULL);
  assert(env != NULL);
  return Plus_eval((Plus*) self, env);               // downcast
}


void* Operator_Plus_apply(void* sum, void* exp, void* params){
  assert(sum != NULL);
  assert(exp != NULL);
  assert(params == NULL); // there should be no params  
  // casting arguments into expected types
  int* sumPtr = (int*) sum;
  Expression* expression = (Expression*) exp;
  if(Expression_isInt(expression)){
    int newInt = ExpInt_toInt((ExpInt*) expression);
    *sumPtr += newInt;
    return sumPtr;
  } 
  else {
    fprintf(stderr,"+: argument is not a valid integer\n");
  }
}


// Override
Expression* Plus_apply(Plus* self, ExpressionComposite* args){
  assert(self != NULL);
  assert(args != NULL);
  int sum = 0;
  ExpressionComposite_foldLeft(args, &sum, Operator_Plus_apply, NULL);
  return (Expression*) ExpInt_new(sum);
}

// overload for vTable initialization
Expression* _Plus_apply(Expression* self, ExpressionComposite* args){
  assert(self != NULL);
  assert(args != NULL);
  return Plus_apply((Plus*) self, args);             // downcast
}


// Override
String* Plus_toString(Plus* self){
  assert(self != NULL);
  String* str = String_new("+");
  return str; // caller has ownership of String. not returning copy
}

// overload for vTable initialization
String* _Plus_toString(Expression* self){
  assert(self != NULL);
  return Plus_toString((Plus*) self);               // downcast
}

// just boiler-plate, passing call to base
int Plus_isInt(Plus* self){
  assert(self != NULL);
  return Expression_isInt((Expression*) self);        // upcast
}


// just boiler-plate, passing call to base
int Plus_isList(Plus* self){
  assert(self != NULL);
  return Expression_isList((Expression*) self);       // upcast
}

void Plus_vTable_delete(ExpressionClass*);            // forward

// Override
void Plus_delete(Plus* self){
  assert(self != NULL);
  Expression* base = (Expression*) self;              //upcast
  assert(base->count > 0);
  base->count--;
  if(base->count == 0){
    assert(base->vTable != NULL);
    Plus_vTable_delete(base->vTable);
    memory_log("deallocating Plus object %lx\n", self);
    free(self);
  } else{
    memory_log("deleting copy of Plus object %lx\n", self);
  }
}

// overload for vTable initialization
void _Plus_delete(Expression* self){
  assert(self != NULL);
  Plus_delete((Plus*) self);                          // downcast
}
// if vTable gets deallocated by destructor, it needs to communicate that
// fact to this function, so it can discard its dangling referrence 'instance'
// Hence the boolean (int) argument.

ExpressionClass* Plus_vTable_new(int killInstance){

  static ExpressionClass* instance = NULL;  // only one instance for Plus
  
  if(killInstance){
    instance = NULL;
    return NULL;
  }

  if(instance != NULL) return Plus_vTable_copy(instance);

  // real memory allocation
  instance = (ExpressionClass*) malloc(sizeof(ExpressionClass));
  assert(instance != NULL);
  memory_log("allocating Plus vTable %lx\n", instance);
  instance->count     = 1;  // first reference
  instance->eval      = _Plus_eval;
  instance->apply     = _Plus_apply;
  instance->toString  = _Plus_toString;
  instance->isList    = _ExpressionLeaf_isList;
  instance->isInt     = _Expression_isInt;
  instance->delete    = _Plus_delete;
  return instance;
}

void Plus_vTable_delete(ExpressionClass* self){
  assert(self != NULL);
  assert(self->count >0);
  self->count--;
  if(self->count == 0){
  memory_log("deallocating Plus vTable %lx\n", self);
  self->eval      = NULL;
  self->apply     = NULL;
  self->toString  = NULL;
  self->isList    = NULL;
  self->isInt     = NULL;
  self->delete    = NULL;
  free(self);
  Plus_vTable_new(1); // setting static 'instance' of singleton to NULL
  }
  else{
    memory_log("deleting copy of Plus vTable %lx\n", self);
  }
}

Plus* Plus_new(){
  Plus* obj = (Plus*) malloc(sizeof(Plus));
  assert(obj != NULL);
  memory_log("allocating Plus object %lx\n",obj);
  // no need to set up anything between Plus and Expression base class
  // so jumping right up to Expression base
  Expression* base = (Expression *) obj;        // upcast
  base->count = 1;                              // first reference
  base->vTable = Plus_vTable_new(0);            // '0' indicates normal use 
  assert(base->vTable != NULL);
  return obj;
}

/******************************************************************************/
/*                            Mult class (level 3)                            */
/******************************************************************************/

struct MultClass_ {
};

struct Mult_ {
  Primitive base;
};

ExpressionClass* Mult_vTable_copy(ExpressionClass* self){
  assert(self != NULL);
  memory_log("making copy of Mult vTable %lx\n", self);
  self->count++;
  return self;
}

Mult* Mult_copy(Mult* self){
  assert(self != NULL);
  memory_log("making copy of Mult object %lx\n", self);
  Expression* base = (Expression*) self;
  base->count++;
  return self;
}

// Override
Expression*  Mult_eval(Mult* self, Environment* env){
  assert(self != NULL);
  assert(env  != NULL);  
  Mult *copy = Mult_copy(self);
  assert(copy != NULL);
  return (Expression*) copy;
}

// overload for vTable initialization
Expression* _Mult_eval(Expression* self, Environment* env){
  assert(self != NULL);
  assert(env != NULL);
  return Mult_eval((Mult*) self, env);               // downcast
}

void* Operator_Mult_apply(void* prod, void* exp, void* params){
  assert(prod != NULL);
  assert(exp != NULL);
  assert(params == NULL); // there should be no params  
  // casting arguments into expected types
  int* prodPtr = (int*) prod;
  Expression* expression = (Expression*) exp;
  if(Expression_isInt(expression)){
    int newInt = ExpInt_toInt((ExpInt*) expression);
    *prodPtr *= newInt;
    return prodPtr;
  } 
  else {
    fprintf(stderr,"*: argument is not a valid integer\n");
  }
}

// Override
Expression* Mult_apply(Mult* self, ExpressionComposite* args){
  assert(self != NULL);
  assert(args != NULL);
  int prod = 1;
  ExpressionComposite_foldLeft(args, &prod, Operator_Mult_apply, NULL);
  return (Expression*) ExpInt_new(prod);
}

// overload for vTable initialization
Expression* _Mult_apply(Expression* self, ExpressionComposite* args){
  assert(self != NULL);
  assert(args != NULL);
  return Mult_apply((Mult*) self, args);             // downcast
}


// Override
String* Mult_toString(Mult* self){
  assert(self != NULL);
  String* str = String_new("*");
  return str; // caller has ownership of String. not returning copy
}

// overload for vTable initialization
String* _Mult_toString(Expression* self){
  assert(self != NULL);
  return Mult_toString((Mult*) self);               // downcast
}

// just boiler-plate, passing call to base
int Mult_isInt(Mult* self){
  assert(self != NULL);
  return Expression_isInt((Expression*) self);        // upcast
}


// just boiler-plate, passing call to base
int Mult_isList(Mult* self){
  assert(self != NULL);
  return Expression_isList((Expression*) self);       // upcast
}

void Mult_vTable_delete(ExpressionClass*);            // forward

// Override
void Mult_delete(Mult* self){
  assert(self != NULL);
  Expression* base = (Expression*) self;              //upcast
  assert(base->count > 0);
  base->count--;
  if(base->count == 0){
    assert(base->vTable != NULL);
    Mult_vTable_delete(base->vTable);
    memory_log("deallocating Mult object %lx\n", self);
    free(self);
  } else{
    memory_log("deleting copy of Mult object %lx\n", self);
  }
}

// overload for vTable initialization
void _Mult_delete(Expression* self){
  assert(self != NULL);
  Mult_delete((Mult*) self);                          // downcast
}
// if vTable gets deallocated by destructor, it needs to communicate that
// fact to this function, so it can discard its dangling referrence 'instance'
// Hence the boolean (int) argument.

ExpressionClass* Mult_vTable_new(int killInstance){

  static ExpressionClass* instance = NULL;  // only one instance for Mult
  
  if(killInstance){
    instance = NULL;
    return NULL;
  }

  if(instance != NULL) return Mult_vTable_copy(instance);

  // real memory allocation
  instance = (ExpressionClass*) malloc(sizeof(ExpressionClass));
  assert(instance != NULL);
  memory_log("allocating Mult vTable %lx\n", instance);
  instance->count     = 1;  // first reference
  instance->eval      = _Mult_eval;
  instance->apply     = _Mult_apply;
  instance->toString  = _Mult_toString;
  instance->isList    = _ExpressionLeaf_isList;
  instance->isInt     = _Expression_isInt;
  instance->delete    = _Mult_delete;
  return instance;
}

void Mult_vTable_delete(ExpressionClass* self){
  assert(self != NULL);
  assert(self->count >0);
  self->count--;
  if(self->count == 0){
  memory_log("deallocating Mult vTable %lx\n", self);
  self->eval      = NULL;
  self->apply     = NULL;
  self->toString  = NULL;
  self->isList    = NULL;
  self->isInt     = NULL;
  self->delete    = NULL;
  free(self);
  Mult_vTable_new(1); // setting static 'instance' of singleton to NULL
  }
  else{
    memory_log("deleting copy of Mult vTable %lx\n", self);
  }
}

Mult* Mult_new(){
  Mult* obj = (Mult*) malloc(sizeof(Mult));
  assert(obj != NULL);
  memory_log("allocating Mult object %lx\n",obj);
  // no need to set up anything between Mult and Expression base class
  // so jumping right up to Expression base
  Expression* base = (Expression *) obj;        // upcast
  base->count = 1;                              // first reference
  base->vTable = Mult_vTable_new(0);            // '0' indicates normal use 
  assert(base->vTable != NULL);
  return obj;
}



/******************************************************************************/
/*                            Nil class (level 2)                             */
/******************************************************************************/

struct NilClass_ {
};

struct Nil_ {
  ExpressionComposite base;
};

ExpressionClass* Nil_vTable_copy(ExpressionClass* self){
  assert(self != NULL);
  memory_log("making copy of Nil primary vTable %lx\n", self);
  self->count++;
  return self;
}

ExpressionCompositeClass* Nil_vTable2_copy(ExpressionCompositeClass* self){
  assert(self != NULL);
  memory_log("making copy of Nil secondary vTable %lx\n", self);
  self->count++;
  return self;
}

Nil* Nil_copy(Nil* self){
  assert(self != NULL);
  memory_log("making copy of Nil object %lx\n", self);
  Expression* base = (Expression*) self;
  base->count++;
  return self;
}

// Override
Expression*  Nil_eval(Nil* self, Environment* env){
  assert(self != NULL);
  assert(env  != NULL);  
  Nil *copy = Nil_copy(self);
  assert(copy != NULL);
  return (Expression*) copy;
}

// overload for vTable initialization
Expression* _Nil_eval(Expression* self, Environment* env){
  assert(self != NULL);
  assert(env != NULL);
  return Nil_eval((Nil*) self, env);               // downcast
}

// Override
Expression* Nil_apply(Nil* self, ExpressionComposite* args){
  assert(self != NULL);
  assert(args != NULL);
  fprintf(stderr,"Nil_apply: Nil is not an operator\n");
  return NULL;
}

// overload for vTable initialization
Expression* _Nil_apply(Expression* self, ExpressionComposite* args){
  assert(self != NULL);
  assert(args != NULL);
  return Nil_apply((Nil*) self, args);             // downcast
}


// Override
String* Nil_toString(Nil* self){
  assert(self != NULL);
  String* str = String_new("Nil");
  return str; // caller has ownership of String. not returning copy
}

// overload for vTable initialization
String* _Nil_toString(Expression* self){
  assert(self != NULL);
  return Nil_toString((Nil*) self);               // downcast
}

// just boiler-plate, passing call to base
int Nil_isInt(Nil* self){
  assert(self != NULL);
  return Expression_isInt((Expression*) self);        // upcast
}


// just boiler-plate, passing call to base
int Nil_isList(Nil* self){
  assert(self != NULL);
  return Expression_isList((Expression*) self);       // upcast
}


// Override
int Nil_isNil(Nil* self){
  assert(self != NULL);
  return 1;
}

// overload for secondary vTable initialization
int _Nil_isNil(ExpressionComposite* self){
  assert(self != NULL);
  return Nil_isNil((Nil*) self);                      // downcast
}

// just boiler-plate, passing call to base
void* Nil_foldLeft(Nil* self, 
    void* init, 
    void* (*operator)(void*, void*, void* params),
    void* params
){
  assert(self != NULL);
  assert(init != NULL);
  assert(operator != NULL);
  return ExpressionComposite_foldLeft(
      (ExpressionComposite*) self, 
      init, 
      operator,
      params 
  );
}

// just boiler-plate, passing call to base
void* Nil_foldRight(Nil* self, 
    void* init, 
    void* operator(void*, void*, void* params),
    void* params
){
  assert(self != NULL);
  assert(init != NULL);
  assert(operator != NULL);
  return ExpressionComposite_foldRight(
      (ExpressionComposite*) self, 
      init, 
      operator,
      params
  );
}

// just boiler-plate, passing call to base
ExpressionComposite* Nil_evalList(Nil* self, Environment* env){
  assert(self != NULL);
  assert(env != NULL);
  ExpressionComposite_evalList((ExpressionComposite*) self, env);
}


void Nil_vTable_delete(ExpressionClass*);             // forward
void Nil_vTable2_delete(ExpressionCompositeClass*);   // forward

// Override
void Nil_delete(Nil* self){
  assert(self != NULL);
  Expression* base = (Expression*) self;              //upcast
  assert(base->count > 0);
  base->count--;
  if(base->count == 0){
    ExpressionComposite* comp = (ExpressionComposite*) self;
    assert(comp->vTable != NULL);
    Nil_vTable2_delete(comp->vTable); // vtable for ExpressionComposite
    assert(base->vTable != NULL);
    Nil_vTable_delete(base->vTable);  // vTable for Expression
    memory_log("deallocating Nil object %lx\n", self);
    free(self);
  } else{
    memory_log("deleting copy of Nil object %lx\n", self);
  }
}

// overload for vTable initialization
void _Nil_delete(Expression* self){
  assert(self != NULL);
  Nil_delete((Nil*) self);                          // downcast
}
// if vTable gets deallocated by destructor, it needs to communicate that
// fact to this function, so it can discard its dangling referrence 'instance'
// Hence the boolean (int) argument.

ExpressionClass* Nil_vTable_new(int killInstance){

  static ExpressionClass* instance = NULL;  // only one instance for Nil
  
  if(killInstance){
    instance = NULL;
    return NULL;
  }

  if(instance != NULL) return Nil_vTable_copy(instance);

  // real memory allocation
  instance = (ExpressionClass*) malloc(sizeof(ExpressionClass));
  assert(instance != NULL);
  memory_log("allocating Nil primary vTable %lx\n", instance);
  instance->count     = 1;  // first reference
  instance->eval      = _Nil_eval;
  instance->apply     = _Nil_apply;
  instance->toString  = _Nil_toString;
  instance->isList    = _ExpressionComposite_isList;
  instance->isInt     = _Expression_isInt;
  instance->delete    = _Nil_delete;
  return instance;
}

ExpressionCompositeClass* Nil_vTable2_new(int killInstance){

  static ExpressionCompositeClass* instance = NULL;  // only one instance for Nil
  
  if(killInstance){
    instance = NULL;
    return NULL;
  }

  if(instance != NULL) return Nil_vTable2_copy(instance);

  // real memory allocation
  instance = (ExpressionCompositeClass*) malloc(sizeof(ExpressionCompositeClass));
  assert(instance != NULL);
  memory_log("allocating Nil secondary vTable %lx\n", instance);
  instance->count     = 1;  // first reference
  instance->isNil = _Nil_isNil;
  return instance;
}



void Nil_vTable_delete(ExpressionClass* self){
  assert(self != NULL);
  assert(self->count >0);
  self->count--;
  if(self->count == 0){
  memory_log("deallocating Nil primary vTable %lx\n", self);
  self->eval      = NULL;
  self->apply     = NULL;
  self->toString  = NULL;
  self->isList    = NULL;
  self->isInt     = NULL;
  self->delete    = NULL;
  free(self);
  Nil_vTable_new(1); // setting static 'instance' of singleton to NULL
  }
  else{
    memory_log("deleting copy of Nil main vTable %lx\n", self);
  }
}

void Nil_vTable2_delete(ExpressionCompositeClass* self){
  assert(self != NULL);
  assert(self->count >0);
  self->count--;
  if(self->count == 0){
  memory_log("deallocating Nil secondary vTable %lx\n", self);
  self->isNil = NULL;
  free(self);
  Nil_vTable2_new(1); // setting static 'instance' of singleton to NULL
  }
  else{
    memory_log("deleting copy of Nil secondary vTable %lx\n", self);
  }
}

Nil* Nil_new(){
  Nil* obj = (Nil*) malloc(sizeof(Nil));
  assert(obj != NULL);
  memory_log("allocating Nil object %lx\n",obj);
  ExpressionComposite* comp = (ExpressionComposite*) obj; // upcast
  comp->vTable = Nil_vTable2_new(0);            // '0' indicates normal use
  assert(comp->vTable != NULL);
  Expression* base = (Expression *) obj;        // upcast
  base->count = 1;                              // first reference
  base->vTable = Nil_vTable_new(0);            // '0' indicates normal use 
  assert(base->vTable != NULL);
  return obj;
}

/******************************************************************************/
/*                           Cons class (level 2)                             */
/******************************************************************************/

struct ConsClass_ {
};

struct Cons_ {
  ExpressionComposite base;
  Expression* car;              // head, first ...
  ExpressionComposite* cdr;     // tail, rest ...
};

ExpressionClass* Cons_vTable_copy(ExpressionClass* self){
  assert(self != NULL);
  memory_log("making copy of Cons primary vTable %lx\n", self);
  self->count++;
  return self;
}

ExpressionCompositeClass* Cons_vTable2_copy(ExpressionCompositeClass* self){
  assert(self != NULL);
  memory_log("making copy of Cons secondary vTable %lx\n", self);
  self->count++;
  return self;
}

Cons* Cons_copy(Cons* self){
  assert(self != NULL);
  memory_log("making copy of Cons object %lx\n", self);
  Expression* base = (Expression*) self;
  base->count++;
  return self;
}

// This is not a virtual method
Expression* Cons_head(Cons* self){
  assert(self != NULL);
  assert(self->car != NULL);
  return Expression_copy(self->car);           // increasing reference count
}

// This is not a virtual method
ExpressionComposite* Cons_tail(Cons* self){
  assert(self != NULL);
  assert(self->cdr != NULL);
  return ExpressionComposite_copy(self->cdr); // increasing reference count
}
// Override
Expression*  Cons_eval(Cons* self, Environment* env){
  assert(self != NULL);
  assert(env  != NULL);  
  ExpressionComposite* vals = ExpressionComposite_evalList(
      (ExpressionComposite*) self, env  // upcast
  );
  assert(!ExpressionComposite_isNil(vals));
  Cons* values = (Cons*) vals;         // downcast, safe in view of assert
  Expression*           operator  = Cons_head(values);
  ExpressionComposite*  arguments = Cons_tail(values);
  Expression*           results   = Expression_apply(operator,arguments);

  ExpressionComposite_delete(vals);
  Expression_delete(operator);
  ExpressionComposite_delete(arguments);
  return results; // caller has ownership of Expression. Not returning copy
}

// overload for vTable initialization
Expression* _Cons_eval(Expression* self, Environment* env){
  assert(self != NULL);
  assert(env != NULL);
  return Cons_eval((Cons*) self, env);               // downcast
}

// Override
Expression* Cons_apply(Cons* self, ExpressionComposite* args){
  assert(self != NULL);
  assert(args != NULL);
  fprintf(stderr,"Cons_apply: Lambda expression are not yet supported\n");
  return NULL;
}

// overload for vTable initialization
Expression* _Cons_apply(Expression* self, ExpressionComposite* args){
  assert(self != NULL);
  assert(args != NULL);
  return Cons_apply((Cons*) self, args);             // downcast
}


void* Operator_Cons_toString(void* str, void* exp, void* params){
  assert(str != NULL);
  assert(exp != NULL);
  assert(params == NULL); // no params
  // casting arguments into their expected types
  String* current = (String*) str;
  Expression* expression = (Expression*) exp;
  String* temp = Expression_toString(expression);
  temp = String_append(temp, String_new(" "));
  return String_append(current, temp);
}

// Override
void* Cons_foldLeft(Cons*, void*,void* (*)(void*,void*,void*), void*);
String* Cons_toString(Cons* self){
  assert(self != NULL);
  String* init = String_new("(");
  String* final = String_new("\b)");
  String* temp = (String*) Cons_foldLeft(self,init,Operator_Cons_toString,NULL);
  return String_append(temp,final);
}

// overload for vTable initialization
String* _Cons_toString(Expression* self){
  assert(self != NULL);
  return Cons_toString((Cons*) self);               // downcast
}

// just boiler-plate, passing call to base
int Cons_isInt(Cons* self){
  assert(self != NULL);
  return Expression_isInt((Expression*) self);        // upcast
}


// just boiler-plate, passing call to base
int Cons_isList(Cons* self){
  assert(self != NULL);
  return Expression_isList((Expression*) self);       // upcast
}


// Override
int Cons_isNil(Cons* self){
  assert(self != NULL);
  return 0;
}

// overload for secondary vTable initialization
int _Cons_isNil(ExpressionComposite* self){
  assert(self != NULL);
  return Cons_isNil((Cons*) self);                      // downcast
}

// just boiler-plate, passing call to base
void* Cons_foldLeft(Cons* self, 
    void* init, 
    void* (*operator)(void*, void*, void* params),
    void* params
){
  assert(self != NULL);
  assert(init != NULL);
  assert(operator != NULL);
  ExpressionComposite_foldLeft(
      (ExpressionComposite*) self, 
      init, 
      operator,
     params 
  );
}

// just boiler-plate, passing call to base
void* Cons_foldRight(Cons* self, 
    void* init, 
    void* (*operator)(void*, void*, void* params),
    void* params
){
  assert(self != NULL);
  assert(init != NULL);
  assert(operator != NULL);
  ExpressionComposite_foldRight(
      (ExpressionComposite*) self, 
      init, 
      operator,
      params 
  );
}

// just boiler-plate, passing call to base
ExpressionComposite* Cons_evalList(Cons* self, Environment* env){
  assert(self != NULL);
  assert(env != NULL);
  ExpressionComposite_evalList((ExpressionComposite*) self, env);
}


void Cons_vTable_delete(ExpressionClass*);             // forward
void Cons_vTable2_delete(ExpressionCompositeClass*);   // forward

// Override
void Cons_delete(Cons* self){
  assert(self != NULL);
  Expression* base = (Expression*) self;              //upcast
  assert(base->count > 0);
  base->count--;
  if(base->count == 0){
    ExpressionComposite* comp = (ExpressionComposite*) self;
    assert(comp->vTable != NULL);
    Cons_vTable2_delete(comp->vTable); // vtable for ExpressionComposite
    assert(base->vTable != NULL);
    Cons_vTable_delete(base->vTable);  // vTable for Expression
    assert(self->car != NULL);
    Expression_delete(self->car);
    self->car = NULL;
    assert(self->cdr != NULL);
    ExpressionComposite_delete(self->cdr);
    self->cdr = NULL;
    memory_log("deallocating Cons object %lx\n", self);
    free(self);
  } else{
    memory_log("deleting copy of Cons object %lx\n", self);
  }
}

// overload for vTable initialization
void _Cons_delete(Expression* self){
  assert(self != NULL);
  Cons_delete((Cons*) self);                          // downcast
}
// if vTable gets deallocated by destructor, it needs to communicate that
// fact to this function, so it can discard its dangling referrence 'instance'
// Hence the boolean (int) argument.

ExpressionClass* Cons_vTable_new(int killInstance){

  static ExpressionClass* instance = NULL;  // only one instance for Cons
  
  if(killInstance){
    instance = NULL;
    return NULL;
  }

  if(instance != NULL) return Cons_vTable_copy(instance);

  // real memory allocation
  instance = (ExpressionClass*) malloc(sizeof(ExpressionClass));
  assert(instance != NULL);
  memory_log("allocating Cons primary vTable %lx\n", instance);
  instance->count     = 1;  // first reference
  instance->eval      = _Cons_eval;
  instance->apply     = _Cons_apply;
  instance->toString  = _Cons_toString;
  instance->isList    = _ExpressionComposite_isList;
  instance->isInt     = _Expression_isInt;
  instance->delete    = _Cons_delete;
  return instance;
}

ExpressionCompositeClass* Cons_vTable2_new(int killInstance){

  static ExpressionCompositeClass* instance = NULL; // only one instance for Cons 
  
  if(killInstance){
    instance = NULL;
    return NULL;
  }

  if(instance != NULL) return Cons_vTable2_copy(instance);

  // real memory allocation
  instance = (ExpressionCompositeClass*) malloc(sizeof(ExpressionCompositeClass));
  assert(instance != NULL);
  memory_log("allocating Cons secondary vTable %lx\n", instance);
  instance->count     = 1;  // first reference
  instance->isNil = _Cons_isNil;
  return instance;
}



void Cons_vTable_delete(ExpressionClass* self){
  assert(self != NULL);
  assert(self->count >0);
  self->count--;
  if(self->count == 0){
  memory_log("deallocating Cons primary vTable %lx\n", self);
  self->eval      = NULL;
  self->apply     = NULL;
  self->toString  = NULL;
  self->isList    = NULL;
  self->isInt     = NULL;
  self->delete    = NULL;
  free(self);
  Cons_vTable_new(1); // setting static 'instance' of singleton to NULL
  }
  else{
    memory_log("deleting copy of Cons main vTable %lx\n", self);
  }
}

void Cons_vTable2_delete(ExpressionCompositeClass* self){
  assert(self != NULL);
  assert(self->count >0);
  self->count--;
  if(self->count == 0){
  memory_log("deallocating Cons secondary vTable %lx\n", self);
  self->isNil = NULL;
  free(self);
  Cons_vTable2_new(1); // setting static 'instance' of singleton to NULL
  }
  else{
    memory_log("deleting copy of Cons secondary vTable %lx\n", self);
  }
}

Cons* Cons_new(Expression *car, ExpressionComposite* cdr){
  // Cons_new takes over ownership of arguments
  assert(car != NULL);
  assert(cdr != NULL);

  Cons* obj = (Cons*) malloc(sizeof(Cons));
  assert(obj != NULL);
  memory_log("allocating Cons object %lx\n", obj);
  memory_log("Cons allocation has car %lx\n", car);
  memory_log("Cons allocation has cdr %lx\n", cdr);

  ExpressionComposite* comp = (ExpressionComposite*) obj; // upcast
  comp->vTable = Cons_vTable2_new(0);            // '0' indicates normal use
  assert(comp->vTable != NULL);
  Expression* base = (Expression *) obj;        // upcast
  base->count = 1;                              // first reference
  base->vTable = Cons_vTable_new(0);             // '0' indicates normal use 
  assert(base->vTable != NULL);
  obj-> car = car;  // caller loses ownership, no copy
  obj->cdr = cdr;   // caller loses ownership, no copy
  return obj;
}
#include "composite.t.c"

int main(int argc, char* argv[], char* envp[]){

    /*
  Expression *two   = (Expression*) ExpInt_new(2);
  Expression *seven = (Expression*) ExpInt_new(7); 
  Expression *five  = (Expression*) ExpInt_new(5); 
  Expression *plus  = (Expression*) lPlus_new();
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
    Plus_test();
    return 0;
  
  }



