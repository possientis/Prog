// Facade Design Pattern

// from GOF: provide a unified interface to a set of interfaces 
// in a subsystem. Facade defines a higher-level interface that 
// makes the subsystem easier to use.
//
//
// In this example (taken from GOF) , we present a compiler system 
// comprised of many complex elements: Scanner, ProgramNodeBuilder, 
// ProgramNode, Parser, RISCCodeGenerator.
//
// All these elements can be used by client code. However, in most
// cases, client code simply wants to provide an input and retrieve
// the compiled output. We implement a 'Facade' for this system via
// the Compiler class and its 'compile' method.

class InputStream {
  private final String filename;

  public InputStream(String filename){
    this.filename = filename;
  }

  public String getFilename(){ return filename; }
}

class BytecodeStream {
  public BytecodeStream(){
  }
}

class Scanner {
  public Scanner(InputStream input){
    System.out.println("creating scanner from " + input.getFilename());
  }
}


class ProgramNodeBuilder {
  private final ProgramNode tree = new ProgramNode();
  
  public ProgramNodeBuilder(){
    System.out.println("creating builder for abstract synrax tree");
  }
  public ProgramNode getRootNode(){
    return tree;
  }
}

class ProgramNode {
  public ProgramNode(){}
  public void traverse(RISCCodeGenerator generator){
    generator.visit(this);
  }
}

class Parser {
  public Parser(){
    System.out.println("creating new parser");
  }
  public void parse(Scanner scanner, ProgramNodeBuilder builder){
    System.out.println("parsing input and building syntax tree");
  }
}

class RISCCodeGenerator {
  public RISCCodeGenerator(BytecodeStream output){
    System.out.println("creating target code generator");
  }
  public void visit(ProgramNode tree){
    System.out.println("generating target code");
  }
}

// now the Facade interface 
class Compiler {
  public Compiler(){
    System.out.println("gcc (Debian 4.9.2-10) 4.9.2 -- fictitious compiler");
  }

  public void compile(InputStream input, BytecodeStream output){

    // creating scanner from InputStream
    Scanner scanner = new Scanner(input);

    // creating builder for abstract syntax tree
    ProgramNodeBuilder builder = new ProgramNodeBuilder();

    // creating Parser
    Parser parser = new Parser();

    // parsing using scanner and builder, hence creating AST
    parser.parse(scanner, builder);

    // creating target code generator
    RISCCodeGenerator generator = new RISCCodeGenerator(output);

    // retrieving abstract syntax tree from builder
    ProgramNode parseTree = builder.getRootNode();

    // generating target code from AST and generator
    parseTree.traverse(generator);

    System.out.println("compilation complete");
  }
}

public class Facade {

  public static void main(String[] args){
    InputStream input = new InputStream("source.c");
    BytecodeStream output = new BytecodeStream();
    Compiler compiler = new Compiler();
    compiler.compile(input, output);
  }

}
