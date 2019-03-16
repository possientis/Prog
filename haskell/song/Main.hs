module  Main
    (   main
    )   where

import FieldElement

a :: FieldElement
a  = field 7 13

b :: FieldElement
b  = field 6 13

one :: FieldElement 
one = field 1 13

main :: IO ()
main = do
    putStrLn $ "a = " ++ show a
    putStrLn $ "b = " ++ show b
    putStrLn $ "a + b = " ++ show (a + b)
    putStrLn $ "a * b = " ++ show (a * b)
    putStrLn $ "-a = " ++ show (-a)
    putStrLn $ "-b = " ++ show (-b)
    putStrLn $ "a^0 = " ++ show (pow a 0)
    putStrLn $ "a^1 = " ++ show (pow a 1)
    putStrLn $ "a^2 = " ++ show (pow a 2)
    putStrLn $ "a^3 = " ++ show (pow a 3)
    putStrLn $ "inv 1 =  " ++ show (inv one)
    putStrLn $ "inv a =  " ++ show (inv a)
    putStrLn $ "inv b =  " ++ show (inv b)
