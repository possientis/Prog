module  Lens
    (
    )   where


import Data.Char
import Control.Lens

ex1 :: String
ex1 = view (_2 . _1) (42, ("hello", False))

ex2 :: Int
ex2 = view (_1 . _2) ((1,2),3)

ex3 :: (Bool, Either String a)
ex3 = set (_2 . _Left) "new" (False, Left "old")

ex4 :: String
ex4 = over (taking 2 worded . traversed) toUpper "testing one two three"

ex5 :: String
ex5 = foldOf (both . each) (["super","cali"],["fragilistic","expialidocious"])

ex6 :: Char
ex6 = view _1 ('a','b')

ex7 :: Char 
ex7 = view _2 ('a','b')

ex8 :: (Char, Char)
ex8 = set _1 'x' ('a','b')

ex9 :: (Int,Int)
ex9 = over _1 (*100) (1,2)
