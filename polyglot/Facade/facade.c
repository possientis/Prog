// Facade Design Pattern
#include <stdio.h>
#include <string.h>
#include <malloc.h>
#include <assert.h>

// from GOF: provide a unified interface to a set of interfaces 
// in a subsystem. Facade defines a higher-level interface that 
// makes the subsystem easier to use.
//
// In this example (taken from GOF) , we present a compiler system 
// comprised of many complex elements: Scanner, ProgramNodeBuilder, 
// ProgramNode, Parser, RISCCodeGenerator.
//
// All these elements can be used by client code. However, in most
// cases client code simply wants to provide an input and retrieve
// the compiled output. We implement a 'Facade' for this system via
// the Compiler class and its 'compile' method.

typedef struct InputStream_         InputStream;
typedef struct BytecodeStream_      BytecodeStream;
typedef struct Scanner_             Scanner;
typedef struct ProgramNode_         ProgramNode;
typedef struct RISCCodeGenerator_   RISCCodeGenerator;
typedef struct ProgramNodeBuilder_  ProgramNodeBuilder;
typedef struct Parser_              Parser;
typedef struct Compiler_            Compiler;

// a type for source code inputs
struct InputStream_ {
  const char* filename;
};

void InputStream_init(InputStream* self, const char* filename){
  assert(self != NULL);
  self->filename = filename;
}

void InputStream_getFilename(InputStream* self, char* buffer, size_t size){
  assert(self != NULL);
  assert(buffer != NULL);
  assert(self->filename != NULL);
  strncpy(buffer, self->filename, size);
}

// a type for compiled target code outputs
struct BytecodeStream_ {};

// a type for scanning: lexical analysis and token stream generation
struct Scanner_ {
};

void Scanner_init(Scanner* self, InputStream* input){
  char filename[128];     // stack allocated
  assert(self != NULL);
  assert(input != NULL);
  InputStream_getFilename(input, filename, 127);
  printf("creating scanner from %s\n", filename);
}

// a type for back end code generation
struct RISCCodeGenerator_ {
};

void RISCCodeGenerator_init(RISCCodeGenerator* self, BytecodeStream* output){
  assert(self != NULL);
  assert(output != NULL);
  printf("creating target code generator\n");
}

void RISCCodeGenerator_visit(RISCCodeGenerator* self, const ProgramNode* tree){
  printf("generating target code\n");
}

// a type for abtract syntax tree
struct ProgramNode_ {
};

void ProgramNode_traverse(const ProgramNode* self, RISCCodeGenerator* generator){
  assert(self != NULL);
  assert(generator != NULL);
  RISCCodeGenerator_visit(generator,self);
}

// a builder type for abstract syntax tree 
struct ProgramNodeBuilder_ {
  const ProgramNode* tree;
};

void ProgramNodeBuilder_init(ProgramNodeBuilder* self){
  assert(self != NULL);
  self->tree = (const ProgramNode*) malloc(sizeof(ProgramNode));
  assert(self->tree != NULL);
  printf("creating builder for abstract syntax tree\n");
}

const ProgramNode*  ProgramNodeBuilder_getRootNode(ProgramNodeBuilder* self){
  assert(self != NULL);
  return self->tree;
}

void ProgramNodeBuilder_destroy(ProgramNodeBuilder* self){
  assert(self != NULL);
  assert(self->tree != NULL);
  free((void*) self->tree);
  self->tree = NULL;
}

// a type parsing tokens and building AST using builder
struct Parser_ {
};

void Parser_init(Parser* self){
  assert(self != NULL);
  printf("creating new parser\n");
}

void Parser_parse(Parser* self, Scanner* scanner, ProgramNodeBuilder* builder){
  printf("parsing input and building syntax tree\n");
}


// now the Facade interface, stripping out the system complexity
// and allowing client to simply call the 'compile' method. 
struct Compiler_ {
};

void Compiler_init(Compiler* self){
  printf("gcc (Debian 4.9.2-10) 4.9.2 -- fictitious compiler\n");
}

void Compiler_compile(Compiler* self, InputStream* input, BytecodeStream* output){
  assert(self != NULL);
  assert(input != NULL);
  assert(output != NULL);
  // creating scanner from InputStream
  Scanner scanner;
  Scanner_init(&scanner, input); 
  // creating builder for abstract syntax tree
  ProgramNodeBuilder builder;
  ProgramNodeBuilder_init(&builder);
  // creating Parser
  Parser parser;
  Parser_init(&parser);
  // parsing using scanner and builder, hence creating AST
  Parser_parse(&parser, &scanner, &builder);
  // creating target code generator
  RISCCodeGenerator generator;
  RISCCodeGenerator_init(&generator, output);
  // retrieving abstract syntax tree from builder
  const ProgramNode* parseTree = ProgramNodeBuilder_getRootNode(&builder);
  // generating target code from AST and generator
  ProgramNode_traverse(parseTree, &generator);
  printf("compilation complete\n");
  ProgramNodeBuilder_destroy(&builder);
}

int main(){
  InputStream input;
  InputStream_init(&input, "source.c");
  BytecodeStream output;
  Compiler compiler;
  Compiler_init(&compiler);
  Compiler_compile(&compiler,&input,&output);
  return 0;
}
