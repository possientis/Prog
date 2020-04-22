{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE InstanceSigs       #-}

module  Cycled
    (   Cycled  (..)
    ,   ex1, ex2, ex3, ex4, ex5, ex6, ex7
    )   where

import Control.Lens


newtype Cycled a = Cycled [a]
    deriving Show

type instance Index (Cycled a)   = Int
type instance IxValue (Cycled a) = a

instance Ixed (Cycled a) where
    ix :: Int -> Traversal' (Cycled a) a
    ix i handler (Cycled xs) = Cycled <$>
        traverseOf (ix (i `mod` length xs)) handler xs

ex1 :: Cycled Char
ex1  = Cycled ['a', 'b', 'c']
 
ex2 :: Maybe Char
ex2 = ex1 ^? ix 1

ex3 :: Maybe Char
ex3 = ex1 ^? ix 10

ex4 :: Maybe Char
ex4 = ex1 ^? ix (-1)

ex5 :: Cycled Char
ex5 = ex1 & ix 0 .~ '!'

ex6 :: Cycled Char
ex6 = ex1 & ix 10 .~ '!'

ex7 :: Cycled Char
ex7 = ex1 & ix (-1) .~ '!'



