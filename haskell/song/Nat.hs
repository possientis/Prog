module  Nat
    (   Nat (..)
    ,   toInteger
    ,   fromInteger
    ,   main
    )   where

import Prelude hiding (toInteger, fromInteger)

data Nat = Z | O Nat | I Nat

toInteger :: Nat -> Integer
toInteger Z     = 0
toInteger (O x) = 2 * toInteger x 
toInteger (I x) = 2 * toInteger x + 1


fromInteger :: Integer -> Nat
fromInteger 0 = Z
fromInteger 1 = I Z
fromInteger x = if even x then O n else I n 
    where n = fromInteger $ x `div` 2

instance Show Nat where
    show = show . toInteger


main :: IO ()
main = do
    print $ Z           -- 0
    print $ I Z         -- 1
    print $ O (I Z)     -- 2
    print $ I (I Z)     -- 3
    print $ O (O (I Z)) -- 4
    print $ map (toInteger . fromInteger) [1..100] == [1..100]


