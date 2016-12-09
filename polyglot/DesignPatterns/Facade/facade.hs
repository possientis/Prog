{- Facade Design Pattern

from GOF: provide a unified interface to a set of interfaces 
in a subsystem. Facade defines a higher-level interface that 
makes the subsystem easier to use.

In this example (taken from GOF) , we present a compiler system 
comprised of many complex elements: Scanner, ProgramNodeBuilder, 
ProgramNode, Parser, RISCCodeGenerator.

All these elements can be used by client code. However, in most
cases client code simply wants to provide an input and retrieve
the compiled output. We implement a 'Facade' for this system via
the Compiler class and its 'compile' method. -}
import Prelude hiding (traverse)
-- a type for source code inputs
data InputStream = InputStream { filename :: String }
newInputStream :: String -> IO InputStream
newInputStream x = return (InputStream x)

-- a type for compiled target code outputs
data BytecodeStream = BytecodeStream
newBytecodeStream :: IO BytecodeStream
newBytecodeStream = return BytecodeStream

-- a type for scanning: lexical analysis and token generation
data Scanner = Scanner InputStream
newScanner :: InputStream -> IO Scanner
newScanner input = do
  putStrLn $ "creating scanner from " ++ filename input
  return (Scanner input)

-- a builder type for abstract syntax tree
data ProgramNodeBuilder = ProgramNodeBuilder { rootNode :: ProgramNode }
newProgramNodeBuilder :: IO ProgramNodeBuilder
newProgramNodeBuilder = do 
  putStrLn "creating builder for abstract syntax tree"
  tree <- newProgramNode
  return (ProgramNodeBuilder tree)

-- a type for asbtract syntax tree
data ProgramNode = ProgramNode
newProgramNode :: IO ProgramNode
newProgramNode = return ProgramNode
traverse :: ProgramNode -> RISCCodeGenerator -> IO()
traverse self generator =  do
  visit generator self
  return ()

-- a type for parsing tokens and building AST using builder
data Parser = Parser
newParser :: IO Parser
newParser = do
  putStrLn "creating new parser"
  return Parser
parse :: Parser -> Scanner -> ProgramNodeBuilder -> IO ()
parse _ _ _ = do
  putStrLn "parsing input and building syntax tree"
  return ()

-- a type for back end code generation
data RISCCodeGenerator = RISCCodeGenerator BytecodeStream
newRISCCodeGenerator :: BytecodeStream -> IO RISCCodeGenerator
newRISCCodeGenerator output = do
  putStrLn "creating target code generator"
  return (RISCCodeGenerator output)
visit :: RISCCodeGenerator -> ProgramNode -> IO ()
visit _ _ = do
  putStrLn "generating target code"
  return ()



-- now the Facade interface, stripping out the system complexity
-- and allowing client to simply call the 'compile' method. 
data Compiler = Compiler
newCompiler :: IO Compiler
newCompiler = do
  putStrLn "gcc (Debian 4.9.2-10) 4.9.2 -- fictitious compiler"
  return Compiler
compile :: Compiler -> InputStream -> BytecodeStream -> IO ()
compile self input output = do
  -- creating scanner from InputStream
  scanner <- newScanner input
  -- creating builder for abstract syntax tree
  builder <- newProgramNodeBuilder
  -- creating Parser
  parser <- newParser
  -- parsing using scanner and builder, hence creating AST
  parse parser scanner builder
  -- creating target code generator
  generator <- newRISCCodeGenerator output
  -- retrieving abstract syntax tree from builder
  let parseTree = rootNode builder 
  -- generating target code from AST and generator
  traverse parseTree generator
  putStrLn "compilation complete"


main :: IO ()
main = do
  input     <- newInputStream "source.c"
  output    <- newBytecodeStream
  compiler  <- newCompiler
  compile compiler input output












