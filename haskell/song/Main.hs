module  Main
    (   main
    )   where

import FieldElement

a :: FieldElement
a  = FieldElement 7 13

b :: FieldElement
b  = FieldElement 6 13


main :: IO ()
main = do
    putStrLn $ "a = " ++ show a
    putStrLn $ "b = " ++ show b
    putStrLn $ "a + b = " ++ show (a + b)
    putStrLn $ "a * b = " ++ show (a * b)
    putStrLn $ "-a = " ++ show (-a)
    putStrLn $ "-b = " ++ show (-b)
