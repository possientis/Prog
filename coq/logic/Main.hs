module  Main
    (   main
    )   where

import Test.QuickCheck

import Fol.Haskell.P
import Lam.Haskell.T
import Haskell.Variable

main :: IO ()
main = do
    putStrLn "\nFirst order logic:"
    sample $ (arbitrary :: Gen (P Var))
    putStrLn "\nSimple lambda calculus"
    sample $ (arbitrary :: Gen (T Var))
    
