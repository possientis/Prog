// Facade Design Pattern
#include <string>
#include <iostream>

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

// a type for source code inputs
class InputStream {
  private:
    const std::string _filename;
  public:
    InputStream(std::string filename):_filename(filename){}
    std::string getFilename() { return _filename; }
};

// a type for compiled target code outputs
class BytecodeStream {};

// a type for scanning: lexical analysis and token stream generation
class Scanner {
  public:
    Scanner(InputStream* input){
      std::cout << "creating scanner from " << input->getFilename() << std::endl;
    }
};

class ProgramNode;

// a type for back end code generation
class RISCCodeGenerator {
  public:
    RISCCodeGenerator(BytecodeStream* output){
      std::cout << "creating target code generator\n";
    }
    void visit(const ProgramNode* tree){
      std::cout << "generating target code\n";
    }
};


// a type for abstract syntax tree
class ProgramNode {
  public:
    void traverse(RISCCodeGenerator* generator) const {
      generator->visit(this);
    }
};


// a builder type for abstract syntax tree
class ProgramNodeBuilder {
  private:
    const ProgramNode* tree;
  public:
    ~ProgramNodeBuilder(){ delete tree; }
    ProgramNodeBuilder(){
      tree = new ProgramNode();
      std::cout << "creating builder for abstract syntax tree\n";
    }
    const ProgramNode* getRootNode(){ return tree; }
};

// a type for parsing tokens and building AST using builder
class Parser {
  public:
    Parser(){
      std::cout << "creating new parser\n";
    }
    void parse(Scanner* scanner, ProgramNodeBuilder* builder){
      std::cout << "parsing input and building syntax tree\n";
    }
};

// now the Facade interface, stripping out the system complexity
// and allowing client to simply call the 'compile' method. 
class Compiler {
  public:
    Compiler(){
      std::cout << "gcc (Debian 4.9.2-10) 4.9.2 -- fictitious compiler\n";
    }
    void compile(InputStream* input, BytecodeStream* output){
      // creating scanner from InputStream
      Scanner scanner(input);
      // creating builder for abstract syntax tree
      ProgramNodeBuilder builder;
      // creating Parser
      Parser parser;
      // parsing using scanner and builder, hence creating AST
      parser.parse(&scanner, &builder);
      // creating target code generator
      RISCCodeGenerator generator(output);
      // retrieving abstract syntax tree from builder
      const ProgramNode* parseTree = builder.getRootNode();
      // generating target code from AST and generator
      parseTree->traverse(&generator);
      std::cout << "compilation complete\n";
    }
};

int main(){
  InputStream input("source.c");
  BytecodeStream output;
  Compiler compiler;
  compiler.compile(&input,&output);
  return 0;
}

