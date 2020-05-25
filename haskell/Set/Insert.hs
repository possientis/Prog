module  Insert
    (   insert
    )   where

import Set

insert :: Set -> Set -> Set
insert x Nil = Cons x Nil
insert x (Cons y ys)
    | x <= y    = Cons y (insert x ys)
    | otherwise = Cons x (Cons y ys) 


