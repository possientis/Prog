{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE TypeInType               #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE ViewPatterns             #-}

module Main
  ( main
  ) where

import Prelude hiding ( lex )

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Data.Char
import Data.List as List
import System.Console.Haskeline
import System.Directory
import Text.PrettyPrint.ANSI.Leijen as Pretty hiding ( (<$>) )
import Type.Reflection

import Stitch.Check
import Stitch.CSE
import Stitch.Data.Nat
import Stitch.Data.Vec
import Stitch.Eval
import Stitch.Exp
import Stitch.Globals
import Stitch.Lex
import Stitch.Monad
import Stitch.Parse
import Stitch.Statement
import Stitch.Unchecked
import Stitch.Utils



-- | The Stitch interpreter
main :: IO ()
main = runInputT defaultSettings $ runStitch $ do
  helloWorld
  loop

-- | Prints welcome message
helloWorld :: Stitch ()
helloWorld = do
  printLine 
    $ text "Welcome to the Stitch interpreter, version" 
   <+> text version 
    <> char '.'
  printLine $ text "Type `:help` at the prompt for the list of commands."

loop :: Stitch ()
loop = do
  m_line <- prompt "λ> "
  case stripWhitespace <$> m_line of
    Nothing          -> quit
    Just (':' : cmd) -> runCommand cmd
    Just str         -> runStmts str
  loop

-- | The current version of stitch
version :: String
version = "1.0"

-------------------------------------------
-- running statements

runStmts :: String -> Stitch ()
runStmts str = stitchE $ do
  toks <- lexM str
  stmts <- parseStmtsM toks
  doStmts stmts

-- | Run a sequence of statements, returning the new global variables
doStmts :: [Statement] -> StitchE Globals
doStmts []     = ask
doStmts (s:ss) = doStmt s $ doStmts ss

-- | Run a 'Statement' and then run another action with the global
-- variables built in the 'Statement'
doStmt :: Statement -> StitchE a -> StitchE a
doStmt (BareExp uexp) thing_inside = check uexp $ \sty e -> do
  printLine $ printValWithType (eval e) sty
  thing_inside
doStmt (NewGlobal g uexp) thing_inside = check uexp $ \sty e -> do
  printLine $ text g <+> char '=' <+> printWithType e sty
  local (extend g sty e) thing_inside

-------------------------------------------
-- commands

-- | Interpret a command (missing the initial ':').
runCommand :: String -> Stitch ()
runCommand = dispatchCommand cmdTable

type CommandTable = [(String, String -> Stitch ())]

dispatchCommand :: CommandTable -> String -> Stitch ()
dispatchCommand table input 
  = case List.filter ((cmd `List.isPrefixOf`) . fst) table of

    []   -> do 
      printLine $ text "Unknown command:" <+> squotes (text cmd)

    [(_, action)] -> action arg

    many -> do 
      printLine $ text "Ambiguous command:" <+> squotes (text cmd)
      printLine 
        $ text "Possibilities:" 
       $$ indent 2 (vcat $ List.map (text . fst) many)

  where (cmd, arg) = List.break isSpace input

cmdTable :: CommandTable
cmdTable = 
  [ ("quit",     quitCmd)
  , ("d-lex",    lexCmd)
  , ("d-parse",  parseCmd)
  , ("load",     loadCmd)
  , ("eval",     evalCmd)
  , ("step",     stepCmd)
  , ("type",     typeCmd)
  , ("all",      allCmd)
  , ("cse-opt",  cseCmd)
  , ("cse-step", cseStepCmd)
  , ("help",     helpCmd)
  ]

quitCmd :: String -> Stitch ()
quitCmd _ = quit

class Reportable a where
  report :: a -> Stitch Globals

instance Reportable Doc where
  report x = printLine x >> get

instance Reportable () where
  report _ = get

instance Reportable Globals where
  report = return

instance {-# OVERLAPPABLE #-} Pretty a => Reportable a where
  report other = printLine (pretty other) >> get

stitchE :: Reportable a => StitchE a -> Stitch ()
stitchE thing_inside = do
  result <- runStitchE thing_inside
  new_globals <- case result of
    Left err -> printLine err >> get
    Right x  -> report x
  put new_globals

parseLex :: String -> StitchE (UExp 'Zero)
parseLex = parseExpM <=< lexM

printWithType :: (Pretty exp, Pretty ty) => exp -> ty -> Doc
printWithType e ty = pretty e <+> colon <+> pretty ty

printValWithType :: ValuePair ty -> TypeRep ty -> Doc
printValWithType v sty = pretty v <+> colon <+> pretty sty

showSteps :: TypeRep ty -> Exp 'VNil ty -> StitchE Int
showSteps sty e1 = do
  printLine $ printWithType e1 sty
  let loop_ num_steps e = case step e of
        Step e' -> do
          printLine $ text "-->" <+> printWithType e' sty
          loop_ (num_steps + 1) e'
        Value _ -> return num_steps
  loop_ 0 e1

lexCmd      :: String -> Stitch ()
parseCmd    :: String -> Stitch ()
evalCmd     :: String -> Stitch ()
stepCmd     :: String -> Stitch ()
typeCmd     :: String -> Stitch ()
allCmd      :: String -> Stitch ()
loadCmd     :: String -> Stitch ()
cseCmd      :: String -> Stitch ()
cseStepCmd  :: String -> Stitch ()
helpCmd     :: String -> Stitch ()

lexCmd = stitchE . lexM

parseCmd = stitchE . parseLex

evalCmd e1 = stitchE $ do
  uexp <- parseLex e1
  check uexp $ \sty e ->
    return $ printValWithType (eval e) sty

stepCmd e1 = stitchE $ do
  uexp <- parseLex e1
  check uexp $ \sty e -> do
    _ <- showSteps sty e
    return ()

typeCmd e1 = stitchE $ do
  uexp <- parseLex e1
  check uexp $ \sty e -> return (printWithType e sty)

allCmd e1 = do
  printLine (text "Small step:")
  _ <- stepCmd e1

  printLine Pretty.empty
  printLine (text "Big step:")
  evalCmd e1

loadCmd (stripWhitespace -> file) = do
  file_exists <- liftIO $ doesFileExist file
  if not file_exists 
    then file_not_found 
    else do
      contents <- liftIO $ readFile file
      runStmts contents
  where
    file_not_found = do
      printLine (text "File not found:" <+> squotes (text file))
      cwd <- liftIO getCurrentDirectory
      printLine (parens (text "Current directory:" <+> text cwd))

cseCmd e1 = stitchE $ do
  uexp <- parseLex e1
  check uexp $ \_sty e -> do
    printLine $ text "Before CSE:" <+> pretty e
    printLine $ text "After CSE: " <+> pretty (cse e)

cseStepCmd e1 = stitchE $ do
  uexp <- parseLex e1
  check uexp $ \sty e -> do
    printLine $ text "Before CSE:" <+> pretty e
    n <- showSteps sty e
    printLine $ text "Number of steps:" <+> pretty n

    printLine $ text "----------------------"

    let e' = cse e
    printLine $ text "After CSE: " <+> pretty e'
    n' <- showSteps sty e'
    printLine $ text "Number of steps:" <+> pretty n'

    return ()

helpCmd _ = mapM_ (printLine . text)
  [ "Available commands:"
  , " :quit             Quits the interpreter"
  , " :load <filename>  Loads a file with ;-separated Stitch statements"
  , " :eval <expr>      Evaluates an expression with big-step semantics"
  , " :step <expr>      Small-steps an expression until it becomes a value"
  , " :type <expr>      Type-check an expression and report the type"
  , " :all <expr>       Combination of :eval and :step"
  , " :cse <expr>       Performs common-subexpression elimination (CSE)"
  , " :cse-step <expr>  Steps an expression both before and after CSE"
  , " :help             Shows this help text"
  , "You may also type an expression to evaluate it, or assign to a global"
  , "variable with `<var> = <expr>"
  ]
