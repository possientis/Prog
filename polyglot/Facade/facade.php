<?php
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
class InputStream {
  private $filename_;
  public function __construct($filename){
    $this->filename_ = $filename;
  }
  public function getFilename(){
    return $this->filename_;
  }
}

// a type for compiled target code outputs
class BytecodeStream{}

// a type for scanning: lexical analysis and token stream generation
class Scanner {
  public function __construct($input){
    echo "creating scanner from ".$input->getFilename()."\n";
  }
}

// a builder type for abstract syntax tree
class ProgramNodeBuilder {
  private $tree;
  public function __construct(){
    $this->tree = new ProgramNode();
    echo "creating builder for abstract syntax tree\n";
  }
  public function getRootNode(){ return $this->tree; }
}

// a type for abstract syntax tree
class ProgramNode {
  public function traverse($generator){
    $generator->visit($this);
  }
}

// a type for parsing tokens and building AST using builder
class Parser {
  public function __construct(){
    echo "creating new parser\n";
  }
  public function parse($scanner, $builder){
    echo "parsing input and building syntax tree\n";
  }
}

// a type for back end code generation
class RISCCodeGenerator {
  public function __construct($output){
    echo "creating target code generator\n";
  }
  public function visit($tree){
    echo "generating target code\n";
  }
}

// now the Facade interface, stripping out the system complexity
// and allowing client to simply call the 'compile' method. 
class Compiler {
  public function __construct(){
    echo "gcc (Debian 4.9.2-10) 4.9.2 -- fictitious compiler\n";
  }
  public function compile($input, $output){
    // creating scanner from InputStream
    $scanner = new Scanner($input);
    // creating builder for abstract syntax tree
    $builder = new ProgramNodeBuilder();
    // creating Parser
    $parser = new Parser();
    // parsing using scanner and builder, hence creating AST
    $parser->parse($scanner, $builder);
    // creating target code generator
    $generator = new RISCCodeGenerator($output);
    // retrieving abstract syntax tree from builder
    $parseTree = $builder->getRootNode();
    // generating target code from AST and generator
    $parseTree->traverse($generator);
    echo "compilation complete"; // newline introduced without '\n'... why? 
  }
}

// main
$input = new InputStream("source.c");
$output = new BytecodeStream();
$compiler = new Compiler();
$compiler->compile($input, $output);

?>

