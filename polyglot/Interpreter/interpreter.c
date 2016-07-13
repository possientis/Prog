// Interpreter Design Pattern
#include <stdio.h>
#include <malloc.h>
#include <assert.h>
#include <string.h>
// from the Gang of Four book:
// "If a particular kind of problem occurs often enough, then it might be
// worthwhile to express instances of the problem as sentences in a simple
// language. Then you can build an interpreter that solves the problem by 
// interpreting these sentences. For example, searching for strings that 
// match a pattern is a common problem. Regular expressions are a standard 
// language for specifying patterns of strings. Rather than building custom 
// algorithms to match each pattern against strings, search algorithms could 
// interpret a regular expression that specifies a set of strings to match."

// Each regular expression r has an associated language L(r) (which is a set
// of strings) defined by the recursion:
//
//  - r = Lit(s)        -> L(r) = {s}
//  - r = And(r1, r2)   -> L(r) = L(r1).L(r2)     (see definition of '.')
//  - r = Or(r1, r2)    -> L(r) = L(r1) U L(r2)
//  - r = Many(r1)      -> L(r) = U_k L(r1)^k     (see definition of '.')
//
//  where given A,B sets of strings the product A.B is defined as the set of 
//  strings A.B = { a ++ b | a in A, b in B }, and where it is understood that
//  A^0 = {""} and A^1 = A. 
//
// Given a regular expression r and a string s, many reasonable questions 
// can be asked in relation to r and s. When using the command 'grep', the
// question being asked is whether there exist a substring s' of s which
// belongs to the language of r. One of the first questions of interest is
// of course whether s itself belongs to L(r).

typedef struct Exp_VT_ Exp_VT;  // virtual tables
typedef struct Exp_ Exp;        // regular expressions
typedef struct Lit_ Lit;        // literal regex 
typedef struct And_ And;        // conjunction of two regex
typedef struct Or_  Or;         // disjunction of two regex 
typedef struct Many_ Many;      // zero or more
typedef enum { LIT=0, AND=1, OR=2, MANY=3 } ExpType;
#define EXP_NUM_TYPES 4


/******************************************************************************/
/*                              Memory log                                    */
/******************************************************************************/

// basic safety scheme against memory leaks
long Exp_log(const char* message, const void* address){
  static long memory_check = 0L;
  // Exp_log(NULL,NULL) returns current memory_check
  if((message == NULL) && (address == NULL)) return memory_check;
  assert(message != NULL);
  assert(address != NULL);
  // message should contain %lx so fprintf expects third 'address' argument
//  fprintf(stderr, message, address);  // uncomment this line when needed
  memory_check ^= (long) address;     // xor-ing address as sanity check
//  fprintf(stderr, "checksum = %ld\n", memory_check);
  return 0L;
}

int Exp_hasMemoryLeak(){
  return Exp_log(NULL, NULL) != 0L;
}


/******************************************************************************/
/*                             Utilities                                      */
/******************************************************************************/

int startsWith(const char *self, const char *prefix)
{
      int len_self = strlen(self);
      int len_prefix = strlen(prefix);
      if(len_self < len_prefix){
        return 0;
      } else {
        return strncmp(self, prefix, len_prefix) == 0;
      }
}

int utils_test(){
  assert(startsWith("abcdef",""));
  assert(startsWith("abcdef","a"));
  assert(startsWith("abcdef","ab"));
  assert(startsWith("abcdef","abc"));
  assert(startsWith("abcdef","abcd"));
  assert(startsWith("abcdef","abcde"));
  assert(startsWith("abcdef","abcdef"));
  assert(!startsWith("abcdef","abcdefx"));
  assert(!startsWith("abcdef","ax"));

  return 0;
}

/******************************************************************************/
/*                               Exp_VT                                       */
/******************************************************************************/

struct Exp_VT_ {
  int refcount;
  int (*to_string)(Exp *self, char* buffer, int size);
  int (*interpret)(Exp *self, const char* input, const char* buffer[], int size);
  void (*delete)(Exp *self);  // virtual destructor
};


Exp_VT* Exp_VT_copy(Exp_VT* self){
  assert(self != NULL);
  Exp_log("Making copy of virtual table %lx\n", self);
  self->refcount++;
  return self;
}

Exp_VT* Exp_VT_new(
  int (*to_string)(Exp* self, char* buffer, int size),
  int (*interpret)(Exp* self, const char* input, const char* buffer[], int size),
  void (*delete)(Exp *self)
  ){
  assert(to_string != NULL);
  assert(interpret != NULL);
  assert(delete != NULL);
  Exp_VT* ptr = (Exp_VT*) malloc(sizeof(Exp_VT));
  assert(ptr != NULL);
  Exp_log("Allocating new virtual table %lx\n", ptr);
  ptr->refcount = 1;
  ptr->to_string = to_string;
  ptr->interpret = interpret;
  ptr->delete = delete;
  return ptr;
}

void Exp_VT_delete(Exp_VT* self){
  assert(self != NULL);
  assert(self->refcount > 0);
  self->refcount--;
  if(self->refcount == 0){
    Exp_log("Deallocating virtual table %lx\n", self);
    self->to_string = NULL;
    self->interpret = NULL;
    self->delete = NULL;
    free(self);
  } else {
    Exp_log("Deleting copy of virtual table %lx\n", self);
  }
}

int stub_to_string(Exp* self, char* buffer, int size){}
int stub_interpret(Exp* self, const char* input, const char* buffer[], int size){}
void stub_delete(Exp* self){
  assert(self != NULL);
  Exp_log("Deallocating regular expression %lx\n", self);
  free(self);
}
Exp_VT* Exp_VT_default(){
  return Exp_VT_new(stub_to_string, stub_interpret, stub_delete);
}


Exp_VT* _Lit_VT_new();
Exp_VT* _And_VT_new();
Exp_VT* _Or_VT_new();
Exp_VT* _Many_VT_new();

// returning singleton instance of virtual table (resetInstance = 0)
// can also be used to clean up virtual table instance (resetInstance = 1)
Exp_VT* Exp_VT_instance(int resetInstance, ExpType type){
  static Exp_VT* instance[EXP_NUM_TYPES] = {NULL, NULL, NULL, NULL};
  assert(resetInstance == 0 || resetInstance == 1);
  if(resetInstance == 0){  // returning virtual table singleton instance
    if(instance[type] == NULL){
      switch(type){
        case LIT:
          instance[type] = _Lit_VT_new();
          break;
        case AND:
          instance[type] = _And_VT_new();
          break;
        case OR:
          instance[type] = _Or_VT_new();
          break;
        case MANY:
          instance[type] = _Many_VT_new();
          break;
        default:
          assert(0);
      }
    }
    assert(instance[type] != NULL);
    return instance[type];
  } else {  // deleting instance if required
    if(instance[type] != NULL){
      Exp_VT_delete(instance[type]);
      instance[type] = NULL;
      return NULL;
    }
  }
}

Lit* Lit_new(const char*);
Exp* Exp_Lit(const char* literal){
  assert(literal != NULL);
  return (Exp*) Lit_new(literal); // upcast
}

And* And_new(Exp*, Exp*);
Exp* Exp_And(Exp* left, Exp* right){
  assert(left != NULL);
  assert(right != NULL);
  return (Exp*) And_new(left, right); // upcast
}

Or* Or_new(Exp*, Exp*);
Exp* Exp_Or(Exp* left, Exp* right){
  assert(left != NULL);
  assert(right != NULL);
  return (Exp*) Or_new(left, right); // upcast
}

Many* Many_new(Exp*);
Exp* Exp_Many(Exp* regex){
  assert(regex != NULL);
  return (Exp*) Many_new(regex); // upcast
}

int Exp_VT_test(){
  /* basic new/copy/delete */
  Exp_VT* vt1 = Exp_VT_default();
  Exp_VT* vt2 = Exp_VT_copy(vt1);
  assert(vt1 == vt2);
  assert(vt1->refcount == 2);
  assert(vt1->to_string == stub_to_string);
  assert(vt1->interpret == stub_interpret);
  assert(vt1->delete == stub_delete);

  Exp_VT_delete(vt2);
  Exp_VT_delete(vt1);
  assert(!Exp_hasMemoryLeak());

  return 0;
}


/******************************************************************************/
/*                                  Exp                                       */
/******************************************************************************/

struct Exp_ {
  int refcount;
  Exp_VT* vtable;
};


Exp* Exp_copy(Exp* self){
  assert(self != NULL);
  self->refcount++;
  Exp_log("Making copy of regular expression %lx\n", self);
  return self;
}

Exp* Exp_new(Exp_VT* vtable){
  assert(vtable != NULL);
  Exp* ptr = (Exp*) malloc(sizeof(Exp));
  assert(ptr != NULL);
  Exp_log("Allocating new regular expression %lx\n", ptr);
  ptr->refcount = 1;
  ptr->vtable = vtable;
  return ptr;
}

void Exp_init(Exp* self, Exp_VT* vtable){
  assert(self != NULL);
  assert(vtable != NULL);
  self->refcount = 1;
  self->vtable = vtable;
}

void Exp_delete(Exp* self){
  assert(self != NULL);
  assert(self->refcount > 0);
  self->refcount--;
  if(self->refcount == 0){
    void (*delete)(Exp*);
    assert(self->vtable != NULL);
    delete = self->vtable->delete;
    assert(delete != NULL);
    delete(self);
  } else {
    Exp_log("Deleting copy of regular expression %lx\n", self);
  }
}

void Exp_destroy(Exp* self){
  assert(self != NULL);
  assert(self->refcount == 0);
  assert(self->vtable != NULL);
  self->vtable = NULL;
}


int Exp_to_string(Exp* self, char* buffer, int size){

  int (*to_string)(Exp*, char*, int);

  if(self == NULL){
    fprintf(stderr, "Exp::to_string: NULL object error\n");
    return -1;
  }
  if(self->vtable == NULL){
    fprintf(stderr, "Exp::to_string: object has no virtual table\n");
    return -1;
  }

  to_string = self->vtable->to_string;
  if(to_string == NULL){
    fprintf(stderr, "Exp::to_string: method not found in virtual table\n");
    return -1;
  }

  return to_string(self, buffer, size);
}

// Given an 'input' string, this method returns 'the' list of all prefixes 
// of the string which belong to the language of the regular expression 
// object. Of course, such a list in only unique up to the order of its elements
//
// Because all the strings returned by the method are prefixes of 'input', 
// each string is characterized by its 'end pointer' in the input string, 
// which is what the function returns via 'buffer'.
//
// Example:
//
// suppose input = "abcdef" and the returned list should be ["a", "abc", ""]
// which is a list of prefixes of "abcdef". Then the function will set:
//
// buffer[0] = p0 (pointer pointing to the 'b' of "abcdef")
// buffer[1] = p1 (pointer pointing to the 'd' of "abcdef")
// buffer[2] = p2 (p2 = input)
// buffer[3] = 0  (indicates termination of the list)
//
// The caller must make sure that 'buffer' is of large enough size
// The 'size' argument is the size of the allocated buffer
//
// This implementation simply manages the indirection of virtual table
//
int Exp_interpret(Exp* self, const char* input, const char* buffer[], int size){
  int (*interpret)(Exp*, const char*, const char* [], int);

  if(self == NULL){
    fprintf(stderr, "Exp::interpret: NULL object error\n");
    return -1;
  }

  if(self->vtable == NULL){
    fprintf(stderr, "Exp::interpret: object has no virtual table\n");
    return -1;
  }

  interpret = self->vtable->interpret;
  if(interpret == NULL){
    fprintf(stderr, "Exp::interpret: method not found in virtual table\n");
    return -1;
  }

  return interpret(self, input, buffer, size);
}


int Exp_test(){
  /* basic new/copy/delete */
  Exp_VT* vt = Exp_VT_default();
  Exp* e1 = Exp_new(vt);
  Exp* e2 = Exp_copy(e1);

  assert(e1 == e2);
  assert(e1->refcount == 2);
  assert(e1->vtable == vt);

  Exp_delete(e2);
  Exp_delete(e1);

  // stack variable
  Exp e;
  Exp_init(&e,vt);
  assert(e.refcount == 1);
  assert(e.vtable == vt);

  Exp_VT_delete(vt);
  assert(!Exp_hasMemoryLeak());

  return 0;
}


/******************************************************************************/
/*                                  Lit                                       */
/******************************************************************************/

struct Lit_ {
  Exp base;
  const char* literal;
};


Lit* Lit_copy(Lit* self){
  assert(self != NULL);
  Exp* base = (Exp*) self;  // upcast
  base->refcount++;
  Exp_log("Making copy of literal regex %lx\n", self);
  return self;
}

// used to initialize virtual table
int _Lit_to_string(Exp* self, char* buffer, int size){

  if(self == NULL){
    fprintf(stderr, "Lit::to_string: NULL object error\n");
    return -1;
  }
  if(buffer == NULL){
    fprintf(stderr, "Lit::to_string: NULL buffer error\n");
    return -1;
  }

  Lit* derived = (Lit*) self;             /* downcast */

  if(derived->literal == NULL){
    fprintf(stderr, "Lit::to_string: object has no literal\n");
    return -1;
  }

  if(strlen(derived->literal) >= size){   /* literal does not fit in buffer */
    fprintf(stderr,"Lit::to_string: buffer overflow error\n");
    return -1;
  }

  /* literal has length strictly less than buffer size, so room for \0 */
  strcpy(buffer, derived->literal);

  return 0;
}

// used to initialize virtual table

int _Lit_interpret(Exp* self, const char* input, const char* buffer[], int size){

  if(self == NULL){
    fprintf(stderr, "Lit::interpret: NULL object error\n");
    return -1;
  }

  if(input == NULL){
    fprintf(stderr, "Lit::interpret: NULL input error\n");
    return -1;
  }

  if(buffer == NULL){
    fprintf(stderr, "Lit::interpret: NULL buffer error\n");
    return -1;
  }
  
  Lit* derived = (Lit*) self; /* downcast */

  if(derived->literal == NULL){
    fprintf(stderr, "Lit::interpret: object has no literal\n");
    return -1;
  }

  if(startsWith(input, derived->literal)){ /* literal is a prefix of input */
    if(size <= 1){
      fprintf(stderr, "Lit::interpret: buffer overflow error\n");
      return -1;
    }
    buffer[0] = input + strlen(derived->literal);
    buffer[1] = NULL;
  } else {
    if(size <= 0){
      fprintf(stderr, "Lit::interpret: buffer overflow error\n");
      return -1;
    }
    buffer[0] = NULL; /* empty list */
  }
    
  return 0;
}

// used to initialize virtual table
void _Lit_delete(Exp* self){
  /* handles deallocation only */
  assert(self != NULL);
  assert(self->refcount == 0);
  Lit* derived = (Lit*) self; // downcast
  derived->literal == NULL;
  Exp_destroy(self);
  Exp_log("Deallocating literal regex %lx\n", derived);
  free(derived);
}

// returning new virtual table object for Lit type
Exp_VT* _Lit_VT_new(){
  return Exp_VT_new(_Lit_to_string, _Lit_interpret, _Lit_delete);
}

// returning singleton instance for Lit virtual table (resetInstance = 0)
// can also be used to clean up virtual table instance (resetInstance = 1)
Exp_VT* _Lit_VT_instance(int resetInstance){
  return Exp_VT_instance(resetInstance, LIT);
}

Lit* Lit_new(const char* literal){
  assert(literal != NULL);
  Lit* ptr = (Lit*) malloc(sizeof(Lit));
  assert(ptr != NULL);
  Exp_log("Allocating new literal regex %lx\n", ptr);
  ptr->literal = literal;
  Exp* base = (Exp*) ptr; // upcast
  Exp_VT* vtable = _Lit_VT_instance(0);
  Exp_init(base,vtable);
  return ptr;
}


void Lit_delete(Lit* self){
  assert(self != NULL);
  Exp* base = (Exp*) self;  // upcast
  Exp_delete(base);         // virtual call
}

int Lit_to_string(Lit* self, char* buffer, int size){
  return Exp_to_string((Exp*) self, buffer, size); /* virtual call */
}

int Lit_interpret(Lit* self, const char* input, const char* buffer[], int size){
  return Exp_interpret((Exp*) self, input, buffer, size); /* virtual call */
}

int Lit_test(){
  /* testing virtual table */
  Exp_VT* vt = _Lit_VT_instance(0); // creation
  _Lit_VT_instance(1);              // deletion
  assert(!Exp_hasMemoryLeak());
  vt = _Lit_VT_instance(0); // creation
  assert(vt != NULL);
  assert(vt->refcount == 1);
  assert(vt->to_string == _Lit_to_string);
  assert(vt->interpret == _Lit_interpret);
  assert(vt->delete == _Lit_delete);
  _Lit_VT_instance(1);      // deletion
  assert(!Exp_hasMemoryLeak());

  const char *lit = "abc";
  Lit* l1 = Lit_new(lit);
  Lit* l2 = Lit_copy(l1);
  assert(l1 == l2);
  assert(l1->literal == lit);
  Exp* base = (Exp*) l1;
  assert(base->refcount == 2);
  assert(base->vtable == _Lit_VT_instance(0));

  // to_string
  char buffer[4];           /* minimal buffer on purpose */
  assert(Lit_to_string(l1, buffer, 4) == 0);
  assert(strcmp(buffer,lit) == 0);
  assert(Exp_to_string(base, buffer, 4) == 0);
  assert(strcmp(buffer,lit) == 0);

  // interpret
  const char* buf[2];
  const char* s = "abcdef";
  const char* t = "not_started_by_abc";
  assert(Lit_interpret(l1, s, buf, 2) == 0);
  assert(buf[0] == s + 3);  /* prefix is "abc" */
  assert(buf[1] == NULL);   /* marking end of list */
  assert(Exp_interpret(base, s, buf, 2) == 0);
  assert(buf[0] == s + 3);  /* prefix is "abc" */
  assert(buf[1] == NULL);   /* marking end of list */
  assert(Exp_interpret(base, s, buf, 2) == 0);
  assert(buf[0] == s + 3);  /* prefix is "abc" */
  assert(buf[1] == NULL);   /* marking end of list */
  assert(Lit_interpret(l1, t, buf, 2) == 0);
  assert(buf[0] == NULL);  /* empty list */
  assert(Exp_interpret(base, t, buf, 2) == 0);
  assert(buf[0] == NULL);  /* empty list */

  Lit_delete(l2);
  Lit_delete(l1);
  _Lit_VT_instance(1);  // cleanup virtual table
  assert(!Exp_hasMemoryLeak());

  return 0;
}


/******************************************************************************/
/*                                 And                                        */
/******************************************************************************/

struct And_ {
  Exp base;
  Exp *left;
  Exp *right;
};

And* And_copy(And* self){
  assert(self != NULL);
  Exp* base = (Exp*) self;  // upcast
  base->refcount++;
  Exp_log("Making copy of And regex %lx\n", self);
  return self;
}

// used to initialize virtual table
int _And_to_string(Exp* self, char* buffer, int size){

  if(self == NULL){
    fprintf(stderr, "And::to_string: NULL object error\n");
    return -1;
  }

  if(buffer == NULL){
    fprintf(stderr, "And::to_string: NULL buffer error\n");
    return -1;
  }

  And* derived = (And*) self;             /* downcast */

  if(derived->left == NULL){
    fprintf(stderr, "And::to_string: object has no left operand\n");
    return -1;
  }

  if(derived->right == NULL){
    fprintf(stderr, "And::to_string: object has no right operand\n");
    return -1;
  }

  /* writing string representation of left operand onto buffer */
  if(Exp_to_string(derived->left, buffer, size) != 0){
    fprintf(stderr, "And::to_string: to_string failure on left operand\n");
    return -1;
  }

  int len_left = strlen(buffer);

  assert(len_left < size);

  /* writing string representation of right operand onto buffer */
  /* following that of the left operand */
  if(Exp_to_string(derived->right, buffer + len_left, size - len_left) != 0){
    fprintf(stderr, "And::to_string: to_string failure on right operand\n");
    return -1;
  }

  return 0;
}

// used to initialize virtual table
int _And_interpret(Exp* self, const char* input, const char* buffer[], int size){

  if(self == NULL){
    fprintf(stderr, "And::interpret: NULL object error\n");
    return -1;
  }

  if(input == NULL){
    fprintf(stderr, "And::interpret: NULL input error\n");
    return -1;
  }

  if(buffer == NULL){
    fprintf(stderr, "And::interpret: NULL buffer error\n");
    return -1;
  }
  
  And* derived = (And*) self; /* downcast */

  if(derived->left == NULL){
    fprintf(stderr, "And::interpret: object has no left operand\n");
    return -1;
  }

  if(derived->right == NULL){
    fprintf(stderr, "And::interpret: object has no right operand\n");
    return -1;
  }



  /*
  if(startsWith(input, derived->literal)){
    if(size <= 1){
      fprintf(stderr, "Lit::interpret: buffer overflow error\n");
      return -1;
    }
    buffer[0] = input + strlen(derived->literal);
    buffer[1] = NULL;
  } else {
    if(size <= 0){
      fprintf(stderr, "Lit::interpret: buffer overflow error\n");
      return -1;
    }
    buffer[0] = NULL;
  }
  */
 
  return 0;
}

// used to initialize virtual table
void _And_delete(Exp* self){
  /* handles deallocation only */
  assert(self != NULL);
  assert(self->refcount == 0);
  And* derived = (And*) self; // downcast
  assert(derived->left != NULL);
  Exp_delete(derived->left);  // virtual call
  assert(derived->right != NULL);
  Exp_delete(derived->right); // virtual call
  Exp_destroy(self);
  Exp_log("Deallocating And regex %lx\n", derived);
  free(derived);
}


// returning new virtual table object for And type
Exp_VT* _And_VT_new(){
  return Exp_VT_new(_And_to_string, _And_interpret, _And_delete);
}

// returning singleton instance for And virtual table (resetInstance = 0)
// can also be used to clean up virtual table instance (resetInstance = 1)
Exp_VT* _And_VT_instance(int resetInstance){
  return Exp_VT_instance(resetInstance, AND);
}

And* And_new(Exp* left, Exp* right){
  assert(left != NULL);
  assert(right != NULL);
  And* ptr = (And*) malloc(sizeof(And));
  assert(ptr != NULL);
  Exp_log("Allocating new And regex %lx\n", ptr);
  ptr->left = left;
  ptr->right = right;
  Exp* base = (Exp*) ptr; // upcast
  Exp_VT* vtable = _And_VT_instance(0);
  Exp_init(base,vtable);
  return ptr;
}

void And_delete(And* self){
  assert(self != NULL);
  Exp* base = (Exp*) self;  // upcast
  Exp_delete(base);         // virtual call
}


int And_to_string(And* self, char* buffer, int size){
  return Exp_to_string((Exp*) self, buffer, size); /* virtual call */
}

int And_interpret(And* self, const char* input, const char* buffer[], int size){
  return Exp_interpret((Exp*) self, input, buffer, size); /* virtual call */
}

int And_test(){
  /* testing virtual table */
  Exp_VT* vt = _And_VT_instance(0); // creation
  _And_VT_instance(1);              // deletion
  assert(!Exp_hasMemoryLeak());
  vt = _And_VT_instance(0); // creation
  assert(vt != NULL);
  assert(vt->refcount == 1);
  assert(vt->to_string == _And_to_string);
  assert(vt->interpret == _And_interpret);
  assert(vt->delete == _And_delete);
  _And_VT_instance(1);      // deletion
  assert(!Exp_hasMemoryLeak());
 
  /* basic new/copy/delete */
  char buffer[7];
  Exp *l1 = Exp_Lit("abc");
  Exp *l2 = Exp_Lit("def");

  And *a1 = And_new(l1, l2);
  And *a2 = And_copy(a1);
  assert(a1 == a2);
  assert(a1->left == l1);
  assert(a1->right == l2);
  Exp* base = (Exp*) a1;
  assert(base->refcount == 2);
  assert(base->vtable == _And_VT_instance(0));

  assert(And_to_string(a1,buffer,7) == 0);
  assert(strcmp(buffer, "abcdef") == 0);

  assert(Exp_to_string(base,buffer,7) == 0);
  assert(strcmp(buffer, "abcdef") == 0);

  And_delete(a2);
  And_delete(a1);
  _And_VT_instance(1);  // cleanup virtual table
  _Lit_VT_instance(1);  // cleanup virtual table
  assert(!Exp_hasMemoryLeak());

  return 0;
}

/******************************************************************************/
/*                                   Or                                       */
/******************************************************************************/

struct Or_ {
  Exp base;
  Exp *left;
  Exp *right;
};

Or* Or_copy(Or* self){
  assert(self != NULL);
  Exp* base = (Exp*) self;  // upcast
  base->refcount++;
  Exp_log("Making copy of Or regex %lx\n", self);
  return self;
}



// used to initialize virtual table
int _Or_to_string(Exp* self, char* buffer, int size){

  if(self == NULL){
    fprintf(stderr, "Or::to_string: NULL object error\n");
    return -1;
  }

  if(buffer == NULL){
    fprintf(stderr, "Or::to_string: NULL buffer error\n");
    return -1;
  }

  Or* derived = (Or*) self;             /* downcast */

  if(derived->left == NULL){
    fprintf(stderr, "Or::to_string: object has no left operand\n");
    return -1;
  }

  if(derived->right == NULL){
    fprintf(stderr, "Or::to_string: object has no right operand\n");
    return -1;
  }

  if(size < 2){
    fprintf(stderr, "Or::to_string: buffer overflow error\n");
    return -1;
  }

  /* writing '(' onto buffer */
  buffer[0] = '('; buffer++; size--;

  /* writing string representation of left operand onto buffer */
  if(Exp_to_string(derived->left, buffer, size) != 0){
    fprintf(stderr, "Or::to_string: to_string failure on left operand\n");
    return -1;
  }

  int len_left = strlen(buffer);
  assert(len_left < size);

  buffer += len_left; size -= len_left;

  if(size < 2){
    fprintf(stderr, "Or::to_string: buffer overflow error\n");
    return -1;
  }

  /* writing '|' onto buffer */
  buffer[0] = '|'; buffer++; size --;

  /* writing string representation of right operand onto buffer */
  if(Exp_to_string(derived->right, buffer , size) != 0){
    fprintf(stderr, "Or::to_string: to_string failure on right operand\n");
    return -1;
  }

  int len_right = strlen(buffer);
  assert(len_right < size);

  buffer += len_right; size -= len_right;

  if(size < 2){
    fprintf(stderr, "Or::to_string: buffer overflow error\n");
    return -1;
  }
   
  /* writing ')' onto buffer */
  buffer[0] = ')'; buffer++; size --;

  /* final \0 */
  buffer[0] = 0;

  return 0;
}

// used to initialize virtual table
int _Or_interpret(Exp* self, const char* input, const char* buffer[], int size){
  // TODO
  return 0;
}

// used to initialize virtual table
void _Or_delete(Exp* self){
  /* handles deallocation only */
  assert(self != NULL);
  assert(self->refcount == 0);
  Or* derived = (Or*) self; // downcast
  assert(derived->left != NULL);
  Exp_delete(derived->left);  // virtual call
  assert(derived->right != NULL);
  Exp_delete(derived->right); // virtual call
  Exp_destroy(self);
  Exp_log("Deallocating Or regex %lx\n", derived);
  free(derived);
}

// returning new virtual table object for Or type
Exp_VT* _Or_VT_new(){
  return Exp_VT_new(_Or_to_string, _Or_interpret, _Or_delete);
}

// returning singleton instance for Or virtual table (resetInstance = 0)
// can also be used to clean up virtual table instance (resetInstance = 1)
Exp_VT* _Or_VT_instance(int resetInstance){
  return Exp_VT_instance(resetInstance, OR);
}

Or* Or_new(Exp* left, Exp* right){
  assert(left != NULL);
  assert(right != NULL);
  Or* ptr = (Or*) malloc(sizeof(Or));
  assert(ptr != NULL);
  Exp_log("Allocating new Or regex %lx\n", ptr);
  ptr->left = left;
  ptr->right = right;
  Exp* base = (Exp*) ptr; // upcast
  Exp_VT* vtable = _Or_VT_instance(0);
  Exp_init(base,vtable);
  return ptr;
}

void Or_delete(Or* self){
  assert(self != NULL);
  Exp* base = (Exp*) self;  // upcast
  Exp_delete(base);         // virtual call
}

int Or_to_string(Or* self, char* buffer, int size){
  return Exp_to_string((Exp*) self, buffer, size); /* virtual call */
}

int Or_interpret(Or* self, const char* input, const char* buffer[], int size){
  return Exp_interpret((Exp*) self, input, buffer, size); /* virtual call */
}

int Or_test(){
  /* testing virtual table */
  Exp_VT* vt = _Or_VT_instance(0); // creation
  _Or_VT_instance(1);              // deletion
  assert(!Exp_hasMemoryLeak());
  vt = _Or_VT_instance(0); // creation
  assert(vt != NULL);
  assert(vt->refcount == 1);
  assert(vt->to_string == _Or_to_string);
  assert(vt->interpret == _Or_interpret);
  assert(vt->delete == _Or_delete);
  _Or_VT_instance(1);      // deletion
  assert(!Exp_hasMemoryLeak());

  /* basic new/copy/delete */
  char buffer[10];
  Exp *l1 = Exp_Lit("abc");
  Exp *l2 = Exp_Lit("def");

  Or *o1 = Or_new(l1, l2);
  Or *o2 = Or_copy(o1);
  assert(o1 == o2);
  assert(o1->left == l1);
  assert(o1->right == l2);
  Exp* base = (Exp*) o1;
  assert(base->refcount == 2);
  assert(base->vtable == _Or_VT_instance(0));


  assert(Or_to_string(o1, buffer, 10) == 0);
  assert(strcmp(buffer, "(abc|def)") == 0);

  assert(Exp_to_string(base, buffer, 10) == 0);
  assert(strcmp(buffer, "(abc|def)") == 0);

  Or_delete(o2);
  Or_delete(o1);
  _Or_VT_instance(1);  // cleanup virtual table
  _Lit_VT_instance(1);  // cleanup virtual table
  assert(!Exp_hasMemoryLeak());

  return 0;
}

/******************************************************************************/
/*                                 Many                                       */
/******************************************************************************/
struct Many_ {
  Exp base;
  Exp* regex;
};

Many* Many_copy(Many* self){
  assert(self != NULL);
  Exp* base = (Exp*) self;  // upcast
  base->refcount++;
  Exp_log("Making copy of Many regex %lx\n", self);
  return self;
}

// used to initialize virtual table
int _Many_to_string(Exp* self, char* buffer, int size){

  if(self == NULL){
    fprintf(stderr, "Many::to_string: NULL object error\n");
    return -1;
  }

  if(buffer == NULL){
    fprintf(stderr, "Many::to_string: NULL buffer error\n");
    return -1;
  }

  Many* derived = (Many*) self;             /* downcast */

  if(derived->regex == NULL){
    fprintf(stderr, "Many::to_string: object has no regex operand\n");
    return -1;
  }

  if(size < 2){
    fprintf(stderr, "Many::to_string: buffer overflow error\n");
    return -1;
  }

  /* writing '(' onto buffer */
  buffer[0] = '('; buffer++; size--;

  /* writing string representation of regex operand onto buffer */
  if(Exp_to_string(derived->regex, buffer, size) != 0){
    fprintf(stderr, "Many::to_string: to_string failure on regex operand\n");
    return -1;
  }

  int len_regex = strlen(buffer);
  assert(len_regex < size);

  buffer += len_regex; size -= len_regex;

  if(size < 3){
    fprintf(stderr, "Many::to_string: buffer overflow error\n");
    return -1;
  }

  /* writing ")*" onto buffer */
  buffer[0] = ')';
  buffer[1] = '*';
  buffer[2] = 0;

  return 0;
}

// used to initialize virtual table
int _Many_interpret(Exp* self, const char* input, const char* buffer[], int size){
  // TODO
  return 0;
}

// used to initialize virtual table
void _Many_delete(Exp* self){
  /* handles deallocation only */
  assert(self != NULL);
  assert(self->refcount == 0);
  Many* derived = (Many*) self; // downcast
  assert(derived->regex != NULL);
  Exp_delete(derived->regex);  // virtual call
  Exp_destroy(self);
  Exp_log("Deallocating Many regex %lx\n", derived);
  free(derived);
}

// returning new virtual table object for Many type
Exp_VT* _Many_VT_new(){
  return Exp_VT_new(_Many_to_string, _Many_interpret, _Many_delete);
}

// returning singleton instance for Many virtual table (resetInstance = 0)
// can also be used to clean up virtual table instance (resetInstance = 1)
Exp_VT* _Many_VT_instance(int resetInstance){
  return Exp_VT_instance(resetInstance, MANY);
}

Many* Many_new(Exp* regex){
  assert(regex != NULL);
  Many* ptr = (Many*) malloc(sizeof(Many));
  assert(ptr != NULL);
  Exp_log("Allocating new Many regex %lx\n", ptr);
  ptr->regex = regex;
  Exp* base = (Exp*) ptr; // upcast
  Exp_VT* vtable = _Many_VT_instance(0);
  Exp_init(base,vtable);
  return ptr;
}

void Many_delete(Many* self){
  assert(self != NULL);
  Exp* base = (Exp*) self;  // upcast
  Exp_delete(base);         // virtual call
}

int Many_to_string(Many* self, char* buffer, int size){
  return Exp_to_string((Exp*) self, buffer, size); /* virtual call */
}

int Many_interpret(Many* self, const char* input, const char* buffer[], int size){
  return Exp_interpret((Exp*) self, input, buffer, size); /* virtual call */
}

int Many_test(){
  /* testing virtual table */
  Exp_VT* vt = _Many_VT_instance(0); // creation
  _Many_VT_instance(1);              // deletion
  assert(!Exp_hasMemoryLeak());
  vt = _Many_VT_instance(0); // creation
  assert(vt != NULL);
  assert(vt->refcount == 1);
  assert(vt->to_string == _Many_to_string);
  assert(vt->interpret == _Many_interpret);
  assert(vt->delete == _Many_delete);
  _Many_VT_instance(1);      // deletion
  assert(!Exp_hasMemoryLeak());

  /* basic new/copy/delete */
  char buffer[7];
  Exp *l = Exp_Lit("abc");

  Many *m1 = Many_new(l);
  Many *m2 = Many_copy(m1);
  assert(m1 == m2);
  assert(m1->regex == l);
  Exp* base = (Exp*) m1;
  assert(base->refcount == 2);
  assert(base->vtable == _Many_VT_instance(0));

  assert(Many_to_string(m1, buffer, 7) == 0);
  assert(strcmp(buffer,"(abc)*") == 0);

  assert(Exp_to_string(base, buffer, 7) == 0);
  assert(strcmp(buffer,"(abc)*") == 0);

  Many_delete(m2);
  Many_delete(m1);
  _Many_VT_instance(1);  // cleanup virtual table
  _Lit_VT_instance(1);  // cleanup virtual table
  assert(!Exp_hasMemoryLeak());

  return 0;
}


/******************************************************************************/
/*                                  Main                                      */
/******************************************************************************/
int test(){


  assert(utils_test() == 0);
  assert(Exp_VT_test() == 0);
  assert(Exp_test() == 0);
  assert(Lit_test() == 0);
  assert(And_test() == 0);
  assert(Or_test() == 0);
  assert(Many_test() == 0);
  assert(!Exp_hasMemoryLeak());

  return 0;
}

void virtual_tables_cleanup(){
  _Lit_VT_instance(1);
  _And_VT_instance(1);
  _Or_VT_instance(1);
  _Many_VT_instance(1);
}

int main(){

  char buffer[22];

  test();

  Exp* a = Exp_Lit("a");
  Exp* b = Exp_Lit("b");
  Exp* c = Exp_Lit("c");

  Exp* aa = Exp_And(Exp_copy(a), Exp_Many(a));
  Exp* bb = Exp_And(Exp_copy(b), Exp_Many(b));
  Exp* cc = Exp_And(Exp_copy(c), Exp_Many(c));

  Exp* regex = Exp_Many(Exp_And(Exp_Or(aa,bb),cc));
  const char* str = "acbbccaaacccbbbbaaaaaccccc";
  assert(Exp_to_string(regex, buffer, 22) == 0);
  printf("regex = %s\n", buffer);
  printf("string = \"%s\"\n", str);
  printf("The recognized prefixes are:\n");


  Exp_delete(regex);
  virtual_tables_cleanup(); // cleaning up virtual tables
  assert(!Exp_hasMemoryLeak());
  return 0;
}
