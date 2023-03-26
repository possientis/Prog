// Facade Design Pattern

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
function InputStream(filename){
  this.filename = filename;
}

// a type for compiled target code outputs
function BytecodeStream(){}

// a type for scanning: lexical analysis and token stream generation
function Scanner(input){
  console.log("creating scanner from " + input.filename);
}

// a builder type for abstract syntax tree
function ProgramNodeBuilder(){
  this.tree = new ProgramNode();
  console.log("creating builder for abstract syntax tree");
}
ProgramNodeBuilder.prototype.rootNode = function(){
  return this.tree;
}

// a type for abstact syntax tree
function ProgramNode(){}
ProgramNode.prototype.traverse = function(generator){
  generator.visit(this);
}

// a type for parsing tokens and building AST using builder
function Parser(){
  console.log("creating new parser");
}
Parser.prototype.parse = function(scanner, builder){
  console.log("parsing input and building syntax tree");
}

// a type for back end code generation
function RISCCodeGenerator(output){
  console.log("creating target code generator");
}

RISCCodeGenerator.prototype.visit = function(tree){
  console.log("generating target code");
}

// now the Facade interface, stripping out the system complexity
// and allowing client to simply call the 'compile' method. 
function Compiler(){
  console.log("gcc (Debian 4.9.2-10) 4.9.2 -- fictitious compiler");
}
Compiler.prototype.compile = function(input, output){
  // creating scanner from InputStream
  scanner = new Scanner(input);
  // creating builder for abstract syntax tree
  builder = new ProgramNodeBuilder();
  // creating Parser
  parser = new Parser();
  // parsing using scanner and builder, hence creating AST
  parser.parse(scanner, builder);
  // creating target code generator
  generator = new RISCCodeGenerator(output);
  // retrieving abstract syntax tree from builder
  parseTree = builder.rootNode();
  // generating target code from AST and generator
  parseTree.traverse(generator);
  console.log("compilation complete");
}

// main
input = new InputStream("source.c");
output = new BytecodeStream();
compiler = new Compiler();
compiler.compile(input, output);





