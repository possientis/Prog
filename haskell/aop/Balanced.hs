{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE DeriveFunctor      #-}

module  Balanced
    (   Tree
    ,   TreeF   (..)
    ,   Info    (..)
    ,   leaf
    ,   node
    ,   size
    ,   info
    ,   t1, t2
    ,   balanced1
    ,   balanced
    )   where

import Data.Functor.Foldable

data TreeF a r = Leaf | Node r a r
    deriving Functor

type Tree a = Fix (TreeF a)

leaf :: Tree a
leaf = Fix Leaf

node :: Tree a -> a -> Tree a -> Tree a
node tl a tr = Fix $ Node tl a tr

t1 :: Tree Int
t1 = node leaf 0 (node leaf 1 leaf)

t2 :: Tree Int
t2 = node (node leaf 0 leaf) 1 (node leaf 0 leaf)

size :: Tree a -> Int
size = cata $ \case
    Leaf        -> 1
    Node n _ m  -> 1 + n + m

-- inefficient, traversing structure too many times
balanced1 :: Tree a -> Bool
balanced1 (Fix Leaf) = True
balanced1 (Fix (Node tl _ tr)) = b1 && b2 && b3 && b4 where
    b1 = balanced1 tl 
    b2 = balanced1 tr
    b3 = 1 + n + m <= 3 * n
    b4 = 3 * n <= 2 * (1 + n + m)
    n = size tl
    m = size tr

data Info = Info
    { infBalanced :: Bool
    , infSize     :: Int
    } deriving (Show)

info :: Tree a -> Info
info = cata $ \case
    Leaf                -> Info { infBalanced = True, infSize = 1}
    Node infL _ infR    -> Info 
        { infBalanced = infBalanced infL && infBalanced infR && s <= p && p <= q
        , infSize = s
        } where
            s = 1 + n + m
            p = 3 * n
            q = 2 * s
            n = infSize infL 
            m = infSize infR

-- Efficient, single traversal based on cata
balanced :: Tree a -> Bool
balanced = infBalanced . info

