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
class InputStream:
    def __init__(self, filename):
        self.filename_ = filename
    @property
    def filename(self):
        return self.filename_
    
# a type for compiled target code outputs
class BytecodeStream: pass

# a type for scanning: lexical analysis and token stream generation 
class Scanner:
    def __init__(self, input):
        print("creating scanner from " + input.filename)

# a builder type for abstract syntax tree
class ProgramNodeBuilder:
    def __init__(self):
        self.tree = ProgramNode()
        print("creating builder for abstract syntax tree")
    @property
    def rootNode(self):
        return self.tree

# a type for abstract syntax tree
class ProgramNode:
    def traverse(self,generator):
        generator.visit(self)

# a type for parsing tokens and building AST using builder
class Parser:
    def __init__(self):
        print("creating new parser")
    def parse(self, scanner, builder):
        print("parsing input and building syntax tree")

# a type for back end code generation
class RISCCodeGenerator:
    def __init__(self, output):
        print("creating target code generator")
    def visit(self, tree):
        print("generating target code")


# now the Facade interface, stripping out the system complexity
# and allowing client to simply call the 'compile' method. 
class Compiler:
    def __init__(self):
        print("gcc (Debian 4.9.2-10) 4.9.2 -- fictitious compiler") 
    def compile(self, input, output):
        # creating scanner from InputStream
        scanner = Scanner(input)
        # creating builder for abstract syntax tree
        builder = ProgramNodeBuilder()
        # creating Parser
        parser = Parser()
        # parsing using scanner and builder, hence creating AST
        parser.parse(scanner, builder)
        # creating target code generator
        generator = RISCCodeGenerator(output)
        # retrieving abstract syntax tree from builder
        parseTree = builder.rootNode
        # generating target code from AST and generator
        parseTree.traverse(generator)
        print("compilation complete")

# main
input = InputStream("source.c")
output = BytecodeStream()
compiler = Compiler()
compiler.compile(input, output)



