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
class InputStream(val _filename: String) {
  def filename = _filename
}

// a type for compiled target code outputs
class BytecodeStream{}

// a type for scannin: lexical analysis and token stream generation
class Scanner(val input: InputStream){
  println("creating scanner from " + input.filename)
}

// a builder type for abstract syntax tree
class ProgramNodeBuilder {
  private val tree: ProgramNode = new ProgramNode
  println("creating builder for abstract syntax tree")
  def rootNode = tree
}

// a type for abstract syntax tree
class ProgramNode {
  def traverse(generator: RISCCodeGenerator) : Unit = {
    generator.visit(this)
  }
}

// a type for parsing tokens and building AST using builder
class Parser {
  println("creating new parser")
  def parse(scanner: Scanner, builder: ProgramNodeBuilder): Unit = {
    println("parsing input and building syntax tree")
  }
}

// a type for back end code generation
class RISCCodeGenerator(val output: BytecodeStream) {
  println("creating target code generator")
  def visit(tree: ProgramNode) : Unit = {
    println("generating target code")
  }
}

// now the Facade interface, stripping out the system complexity
// and allowing client to simply call the 'compile' method. 
class Compiler {
  println("gcc (Debian 4.9.2-10) 4.9.2 -- fictitious compiler");
  def compile(input: InputStream, output: BytecodeStream): Unit = {
    // creating scanner from InputStream
    val scanner = new Scanner(input);
    // creating builder for abstract syntax tree
    val builder = new ProgramNodeBuilder();
    // creating Parser
    val parser = new Parser();
    // parsing using scanner and builder, hence creating AST
    parser.parse(scanner, builder);
    // creating target code generator
    val generator = new RISCCodeGenerator(output);
    // retrieving abstract syntax tree from builder
    val parseTree = builder.rootNode;
    // generating target code from AST and generator
    parseTree.traverse(generator);
    println("compilation complete");
  }
}



// main
object Facade {
  def main(args: Array[String]){
    val input = new InputStream("source.c");
    val output = new BytecodeStream();
    val compiler = new Compiler();
    compiler.compile(input, output);
  }
}
