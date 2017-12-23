import Language.Haskell.Interpreter

foo :: Interpreter String
foo = eval "(\\x -> x) 1"


example :: IO (Either InterpreterError String)
example = runInterpreter foo
