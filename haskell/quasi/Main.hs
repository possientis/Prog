{-# LANGUAGE QuasiQuotes        #-}

module  Main
    (   main
    )   where

import Quote
import Expr

e1 :: Expr
e1 = [expr|1 + 3 + 5|]

e2 :: Expr
e2 = [expr|1 + 3*(5 + 2)|]

eval' :: Expr -> Integer 
eval' [expr|$int:x|] = x
eval' [expr|$exp:x + $exp:y|] = eval' x + eval' y
eval' [expr|$exp:x - $exp:y|] = eval' x - eval' y
eval' [expr|$exp:x * $exp:y|] = eval' x * eval' y
eval' [expr|$exp:x / $exp:y|] = eval' x `div` eval' y
eval' _                       = error "Evaluation of antiquotes not supported"


main :: IO ()
main = do
    putStrLn $ "eval  e1 = " ++ show (eval  e1)
    putStrLn $ "eval' e1 = " ++ show (eval' e1)
    putStrLn $ "eval  e2 = " ++ show (eval  e2)
    putStrLn $ "eval' e2 = " ++ show (eval' e2)

