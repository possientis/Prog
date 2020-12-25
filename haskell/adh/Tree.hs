module  Tree
    (   Tree    (..)
    ,   size
    ,   node
    ,   leaf
    )   where

-- Binary tree which stores its own size (number of leaves)
data Tree a = Leaf a | Node Int (Tree a) (Tree a)

-- invariant must be repected, otherwise size is wrong
size :: Tree a -> Int
size (Leaf _) = 1
size (Node n _ _) = n

node :: Tree a -> Tree a -> Tree a
node t1 t2 = Node (size t1 + size t2) t1 t2

leaf :: a -> Tree a
leaf = Leaf

