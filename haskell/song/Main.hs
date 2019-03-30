module  Main
    (   main
    )   where

import Prelude hiding ((+),(*))
import F13
import Field

a :: F13
a  = F13 7

b :: F13
b  = F13 6

main :: IO ()
main = do
    putStrLn $ "a = " ++ show a
    putStrLn $ "b = " ++ show b
    putStrLn $ "a + b = " ++ show (a + b)
    putStrLn $ "a * b = " ++ show (a * b)
    putStrLn $ "-a = " ++ show (neg a)
    putStrLn $ "-b = " ++ show (neg b)
    putStrLn $ "a^(-2) = " ++ show (pow a (-2))
    putStrLn $ "a^(-1) = " ++ show (pow a (-1))
    putStrLn $ "a^0 = " ++ show (pow a 0)
    putStrLn $ "a^1 = " ++ show (pow a 1)
    putStrLn $ "a^2 = " ++ show (pow a 2)
    putStrLn $ "a^3 = " ++ show (pow a 3)
    putStrLn $ "inv 1 =  " ++ show (inv one :: F13)
    putStrLn $ "inv a =  " ++ show (inv a)
    putStrLn $ "inv b =  " ++ show (inv b)
