{-# LANGUAGE TypeOperators #-}

data Tree = Top | Tree :*: Tree | Tree :->: Tree


ex :: Tree
ex = Top :->: ex


