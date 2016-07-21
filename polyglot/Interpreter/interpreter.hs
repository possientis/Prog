-- Interpreter Design Pattern
import Data.List
import Test.HUnit.Base
-- from the Gang of Four book:
-- "If a particular kind of problem occurs often enough, then it might be
-- worthwhile to express instances of the problem as sentences in a simple
-- language. Then you can build an interpreter that solves the problem by 
-- interpreting these sentences. For example, searching for strings that 
-- match a pattern is a common problem. Regular expressions are a standard 
-- language for specifying patterns of strings. Rather than building custom 
-- algorithms to match each pattern against strings, search algorithms could 
-- interpret a regular expression that specifies a set of strings to match."

-- Each regular expression r has an associated language L(r) (which is a set
-- of strings) defined by the recursion:
--
--  - r = Lit(s)        -> L(r) = {s}
--  - r = And(r1, r2)   -> L(r) = L(r1).L(r2)     (see definition of '.')
--  - r = Or(r1, r2)    -> L(r) = L(r1) U L(r2)
--  - r = Many(r1)      -> L(r) = U_k L(r1)^k     (see definition of '.')
--
--  where given A,B sets of strings the product A.B is defined as the set of 
--  strings A.B = { a ++ b | a in A, b in B }, and where it is understood that
--  A^0 = {""} and A^1 = A. 
--
-- Given a regular expression r and a string s, many reasonable questions 
-- can be asked in relation to r and s. When using the command 'grep', the
-- question being asked is whether there exist a substring s' of s which
-- belongs to the language of r. One of the first questions of interest is
-- of course whether s itself belongs to L(r).

data Exp
  = Lit { literal:: String }
  | And { left :: Exp, right :: Exp }
  | Or  { left :: Exp, right :: Exp }
  | Many{ regex :: Exp}
  deriving Eq

newLit :: String -> Exp
newLit  = Lit

newAnd :: Exp -> Exp -> Exp
newAnd  = And

newOr :: Exp -> Exp -> Exp
newOr  = Or

newMany :: Exp -> Exp
newMany  = Many

instance Show Exp where
  show (Lit s)     = s
  show (And e1 e2) = (show e1) ++ (show e2)
  show (Or e1 e2)  = "(" ++ (show e1) ++ "|" ++ (show e2) ++ ")"
  show (Many r)    = "(" ++ (show r) ++ ")*"

-- Given a string, this method returns 'the' list of all prefixes of the string
-- which belong to the language of the regular expression object. Of course,
-- such a list in only unique up to the order of its elements
interpret :: Exp -> String -> [String]
interpret (Lit s) input
  | isPrefixOf s input = [s]
  | otherwise          = [] 
interpret (And e1 e2) input = [s1 ++ s2 | 
  s1 <- (interpret e1 input), 
  s2 <- (interpret e2 (drop (length s1) input))]
interpret (Or e1 e2) input = interpret e1 input ++ interpret e2 input
interpret (Many r) input = [""] ++ [s1 ++ s2 |
  s1 <- (interpret r input), s1 /= "",
  s2 <- (interpret (Many r) (drop (length s1) input))]  -- recursive call

recognize :: Exp -> String -> Bool
recognize r input = elem input (interpret r input) 


testAll :: IO ()
testAll = do
  testLit
  testAnd
  testOr
  testMany

testLit :: IO ()
testLit = do
  let lit = newLit "abc"
  assertEqual "testLit: literal"    (literal lit)             "abc"
  assertEqual "testLit: show"       (show lit)                "abc"
  assertEqual "testLit: interpret"  (interpret lit "")        []
  assertEqual "testLit: interpret"  (interpret lit "a")       []
  assertEqual "testLit: interpret"  (interpret lit "ab")      []
  assertEqual "testLit: interpret"  (interpret lit "abc")     ["abc"]
  assertEqual "testLit: interpret"  (interpret lit "abcx")    ["abc"]
  assertEqual "testLit: recognize"  (recognize lit "")        False
  assertEqual "testLit: recognize"  (recognize lit "a")       False
  assertEqual "testLit: recognize"  (recognize lit "ab")      False
  assertEqual "testLit: recognize"  (recognize lit "abc")     True
  assertEqual "testLit: recognize"  (recognize lit "abcx")    False

testAnd :: IO ()
testAnd = do
  let a = newAnd (newLit "abc") (newLit "def")
  assertEqual "testAnd: left"       (left a)                  (newLit "abc")  
  assertEqual "testAnd: right"      (right a)                 (newLit "def")  
  assertEqual "testAnd: show"       (show a)                  "abcdef"
  assertEqual "testAnd: interpret"  (interpret a "")          []
  assertEqual "testAnd: interpret"  (interpret a "a")         []
  assertEqual "testAnd: interpret"  (interpret a "ab")        []
  assertEqual "testAnd: interpret"  (interpret a "abc")       []
  assertEqual "testAnd: interpret"  (interpret a "abcd")      []
  assertEqual "testAnd: interpret"  (interpret a "abcde")     []
  assertEqual "testAnd: interpret"  (interpret a "abcdef")    ["abcdef"]
  assertEqual "testAnd: interpret"  (interpret a "abcdefx")   ["abcdef"]
  assertEqual "testAnd: recognize"  (recognize a "")          False
  assertEqual "testAnd: recognize"  (recognize a "a")         False
  assertEqual "testAnd: recognize"  (recognize a "ab")        False
  assertEqual "testAnd: recognize"  (recognize a "abc")       False
  assertEqual "testAnd: recognize"  (recognize a "abcd")      False
  assertEqual "testAnd: recognize"  (recognize a "abcde")     False
  assertEqual "testAnd: recognize"  (recognize a "abcdef")    True
  assertEqual "testAnd: recognize"  (recognize a "abcdefx")   False

testOr :: IO ()
testOr = do
  let o = newOr (newLit "abc") (newLit "def")
  assertEqual "testOr: left"        (left o)                  (newLit "abc")  
  assertEqual "testOr: right"       (right o)                 (newLit "def")  
  assertEqual "testOr: show"        (show o)                  "(abc|def)"
  assertEqual "testOr: interpret"   (interpret o "")          []
  assertEqual "testOr: interpret"   (interpret o "a")         []
  assertEqual "testOr: interpret"   (interpret o "ab")        []
  assertEqual "testOr: interpret"   (interpret o "abc")       ["abc"]
  assertEqual "testOr: interpret"   (interpret o "abcx")      ["abc"]
  assertEqual "testOr: interpret"   (interpret o "d")         []
  assertEqual "testOr: interpret"   (interpret o "de")        []
  assertEqual "testOr: interpret"   (interpret o "def")       ["def"]
  assertEqual "testOr: interpret"   (interpret o "defx")      ["def"]
  assertEqual "testOr: recognize"   (recognize o "")          False
  assertEqual "testOr: recognize"   (recognize o "a")         False
  assertEqual "testOr: recognize"   (recognize o "ab")        False
  assertEqual "testOr: recognize"   (recognize o "abc")       True
  assertEqual "testOr: recognize"   (recognize o "abcx")      False
  assertEqual "testOr: recognize"   (recognize o "d")         False
  assertEqual "testOr: recognize"   (recognize o "de")        False
  assertEqual "testOr: recognize"   (recognize o "def")       True
  assertEqual "testOr: recognize"   (recognize o "defx")      False

testMany :: IO ()
testMany = do
  let m = newMany (newLit "abc")
  assertEqual "testMany: regex"     (regex m)                 (newLit "abc")  
  assertEqual "testMany: show"      (show m)                  "(abc)*"
  assertEqual "testMany: interpret" (interpret m "")          [""]
  assertEqual "testMany: interpret" (interpret m "a")         [""]
  assertEqual "testMany: interpret" (interpret m "ab")        [""]
  assertEqual "testMany: interpret" (interpret m "abc")       ["","abc"]
  assertEqual "testMany: interpret" (interpret m "abca")      ["","abc"]
  assertEqual "testMany: interpret" (interpret m "abcab")     ["","abc"]
  assertEqual "testMany: interpret" (interpret m "abcabc")    ["","abc","abcabc"]
  assertEqual "testMany: interpret" (interpret m "abcabca")   ["","abc","abcabc"]
  assertEqual "testMany: interpret" (interpret m "abcabcab")  ["","abc","abcabc"]
  assertEqual "testMany: interpret" 
    (interpret m "abcabcabc")   ["","abc","abcabc","abcabcabc"]
  assertEqual "testMany: interpret" 
    (interpret m "abcabcabcx")  ["","abc","abcabc","abcabcabc"]
  assertEqual "testMany: recognize" (recognize m "")          True
  assertEqual "testMany: recognize" (recognize m "a")         False
  assertEqual "testMany: recognize" (recognize m "ab")        False
  assertEqual "testMany: recognize" (recognize m "abc")       True
  assertEqual "testMany: recognize" (recognize m "abca")      False
  assertEqual "testMany: recognize" (recognize m "abcab")     False
  assertEqual "testMany: recognize" (recognize m "abcabc")    True
  assertEqual "testMany: recognize" (recognize m "abcabca")   False
  assertEqual "testMany: recognize" (recognize m "abcabcab")  False
  assertEqual "testMany: recognize" (recognize m "abcabcabc") True
  assertEqual "testMany: recognize" (recognize m "abcabcabcx")False


main = let
  a = newLit "a"
  b = newLit "b"
  c = newLit "c"
  aa = newAnd a (newMany a) -- one or more 'a'
  bb = newAnd b (newMany b) -- one or more 'b'
  cc = newAnd c (newMany c) -- one or more 'c'
  regex = newMany (newAnd (newOr aa bb) cc)
  string = "acbbccaaacccbbbbaaaaaccccc"
  in do
    testAll
    putStrLn $ "regex = " ++ (show regex)
    putStrLn $ "string = \"" ++ string ++ "\""
    putStrLn "The recognized prefixes are:"
    let result = map  (\s -> "\"" ++ s ++ "\"")
                      (filter (recognize regex) 
                              (map  (flip take string) 
                                    [0..(length string)]))

    putStrLn $ "[" ++ intercalate ", " result ++ "]"







