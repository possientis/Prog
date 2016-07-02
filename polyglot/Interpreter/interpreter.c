// Interpreter Design Pattern
#include <stdio.h>
#include <malloc.h>
#include <assert.h>
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
  fprintf(stderr, message, address);  // uncomment this line when needed
  memory_check ^= (long) address;     // xor-ing address as sanity check
//  fprintf(stderr, "checksum = %ld\n", memory_check);
  return 0L;
}

int Exp_hasMemoryLeak(){
  return Exp_log(NULL, NULL) != 0L;
}



/******************************************************************************/
/*                               Exp_VT                                       */
/******************************************************************************/

struct Exp_VT_ {
  int refcount;
  int (*to_string)(Exp *self, char* buffer, int size);
  int (*interpret)(Exp *self, const char* input, const char* *buffer, int size);
  void (*delete)(Exp *self);  // virtual destructor
};





/******************************************************************************/
/*                                  Exp                                       */
/******************************************************************************/


struct Exp_ {
  int refcount;
};


/******************************************************************************/
/*                                  Main                                      */
/******************************************************************************/

int main(){

  assert(!Exp_hasMemoryLeak());

  return 0;
}
