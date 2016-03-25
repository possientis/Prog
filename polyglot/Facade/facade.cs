// Facade Design Pattern
using System;
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
  private readonly string filename;
  public InputStream(string filename){ this.filename = filename; }
  public string Filename { get { return filename; } }
}

// a type for compiled target code outputs
class BytecodeStream {
  public BytecodeStream(){
  }
}

// a type for scanning: lexical analysis and token stream generation
class Scanner {
  public Scanner(InputStream input){
    Console.WriteLine("creating scanner from " + input.Filename);
  }
}

// a type for building the abstract syntax tree
class ProgramNodeBuilder {
  private readonly ProgramNode tree = new ProgramNode();
  public ProgramNodeBuilder(){
    Console.WriteLine("creating builder for abstract syntax tree");
  }
  public ProgramNode GetRootNode(){ return tree; }
}

// a type for abstract syntax tree
class ProgramNode {
  public ProgramNode(){}
  public void Traverse(RISCCodeGenerator generator){
    generator.Visit(this);
  }
}

// a type for parsing tokens and building AST using builder 
class Parser {
  public Parser(){
    Console.WriteLine("creating new parser");
  }
  public void Parse(Scanner scanner, ProgramNodeBuilder builder){
    Console.WriteLine("parsing input and building syntax tree");
  }
}

// a type for back end code generation
class RISCCodeGenerator {
  public RISCCodeGenerator(BytecodeStream output){
    Console.WriteLine("creating target code generator");
  }
  public void Visit(ProgramNode tree){
    Console.WriteLine("generating target code");
  }
}

// now the Facade interface, stripping out the system complexity
// and allowing client to simply call the 'Compile' method. 
class Compiler {
  public Compiler(){
    Console.WriteLine("gcc (Debian 4.9.2-10) 4.9.2 -- fictitious compiler");
  }
  public void Compile(InputStream input, BytecodeStream output){
    // creating scanner from InputStream
    Scanner scanner = new Scanner(input);
    // creating builder for abstract syntax tree
    ProgramNodeBuilder builder = new ProgramNodeBuilder();
    // creating Parser
    Parser parser = new Parser();
    // parsing using scanner and builder, hence creating AST
    parser.Parse(scanner, builder);
    // creating target code generator
    RISCCodeGenerator generator = new RISCCodeGenerator(output);
    // retrieving abstract syntax tree from builder
    ProgramNode parseTree = builder.GetRootNode();
    // generating target code from AST and generator
    parseTree.Traverse(generator);
    Console.WriteLine("compilation complete");
  }
}

// main
public class Facade {
  public static void Main(string[] args){
    InputStream input = new InputStream("source.c");
    BytecodeStream output = new BytecodeStream();
    Compiler compiler = new Compiler();
    compiler.Compile(input, output);
  }
}
