# Facade Design Pattern

# from GOF: provide a unified interface to a set of interfaces 
# in a subsystem. Facade defines a higher-level interface that 
# makes the subsystem easier to use.
#
# In this example (taken from GOF) , we present a compiler system 
# comprised of many complex elements: Scanner, ProgramNodeBuilder, 
# ProgramNode, Parser, RISCCodeGenerator.
#
# All these elements can be used by client code. However, in most
# cases client code simply wants to provide an input and retrieve
# the compiled output. We implement a 'Facade' for this system via
# the Compiler class and its 'compile' method.

# a type for code inputs
class InputStream
  attr_reader :filename
  def initialize(filename)
    @filename = filename
  end
end

# a type for compiled target code outputs
class BytecodeStream
end

# a type for scanning: lexical analysis and token stream generation
class Scanner
  def initialize(input)
    puts "creating scanner from " + input.filename 
  end
end

# a builder type for abstract syntax tree
class ProgramNodeBuilder
  attr_reader :rootNode
  def initialize()
    @tree = ProgramNode.new
    puts "creating builder for abstract syntax tree" 
  end
  def rootNode
    @tree
  end
end

# a type for abstract syntax tree
class ProgramNode
  def traverse(generator)
    generator.visit(self)
  end
end

# a type for parsing tokens and building AST using builder
class Parser
  def initialize()
    puts "creating new parser" 
  end
  def parse(scanner,builder)
    puts "parsing input and building syntax tree" 
  end
end

# a type for back end code generation
class RISCCodeGenerator
  def initialize(output)
    puts "creating target code generator" 
  end
  def visit(tree)
    puts "generating target code" 
  end
end


# now the Facade interface, stripping out the system complexity
# and allowing client to simply call the 'compile' method. 
class Compiler
  def initialize()
    puts "gcc (Debian 4.9.2-10) 4.9.2 -- fictitious compiler" 
  end
  def compile(input, output)
    # creating scanner from InputStream
    scanner = Scanner.new(input)
    # creating builder for abstract syntax tree
    builder = ProgramNodeBuilder.new
    # creating Parser
    parser = Parser.new
    # parsing using scanner and builder, hence creating AST
    parser.parse(scanner, builder)
    # creating target code generator
    generator = RISCCodeGenerator.new(output)
    # retrieving abstract syntax tree from builder
    parseTree = builder.rootNode
    # generating target code from AST and generator
    parseTree.traverse(generator)
    puts "compilation complete"
  end
end

# main
input = InputStream.new "source.c"
output = BytecodeStream.new
compiler = Compiler.new
compiler.compile(input, output)






