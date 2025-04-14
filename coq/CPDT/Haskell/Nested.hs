module  Haskell.Nested
    (   Tree    (..)
    ,   fold
    )   where

import Data.Monoid

data Tree a = Node a [Tree a]


instance Functor Tree where
    fmap f (Node x ts) = Node (f x) $ map (fmap f) ts

instance Foldable Tree where
    foldMap f (Node x ts) = f x <> (mconcat $ map (foldMap f) ts)

fold :: (a -> [b] -> b) -> Tree a -> b
fold f (Node x ts) = f x $ map (fold f) ts
