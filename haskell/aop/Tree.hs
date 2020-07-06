module  Tree
    (   Tree    (..)
    ,   foldTree
    ,   sizeTree
    ,   depthTree
    ,   toList
    ,   fromList
    ,   Forest  (..)
    ,   Tree'   (..)
    ,   foldTree'
    ,   foldForest
    )   where

import Prelude hiding 
    (   (+)
    ,   max
    )
 
import Nat

data Tree a = Tip a | Bin (Tree a) (Tree a)


foldTree :: (a -> b) -> (b -> b -> b) -> Tree a -> b 
foldTree f _ (Tip x) = f x
foldTree f g (Bin t1 t2) = g (foldTree f g t1) (foldTree f g t2)

mapTree :: (a -> b) -> Tree a -> Tree b
mapTree f = foldTree (Tip . f) Bin

sizeTree :: Tree a -> Nat
sizeTree = foldTree (const one) (+)

depthTree :: Tree a -> Nat
depthTree = foldTree (const zero) (\n m -> Succ (max n m))

instance Functor Tree where
    fmap = mapTree


data Tree' a = Fork a (Forest a)

data Forest a = Nil | Grow (Tree' a) (Forest a)

toList :: Forest a -> [Tree' a]
toList Nil = []
toList (Grow t ts) = t : toList ts

fromList :: [Tree' a] -> Forest a
fromList [] = Nil
fromList (t : ts) = Grow t (fromList ts)

foldTree' :: (a -> c -> b) -> c -> (b -> c -> c) -> Tree' a -> b
foldTree' g c h (Fork x f) = g x (foldForest g c h f)

foldForest :: (a -> c -> b) -> c -> (b -> c -> c) -> Forest a -> c
foldForest _ c _ Nil = c
foldForest g c h (Grow t f) = h (foldTree' g c h t) (foldForest g c h f)

