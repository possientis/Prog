{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

import Data.Functor.Identity

data Tree a = Node a [Tree a]
    deriving (Show, Functor, Foldable, Traversable)


tree :: Tree Integer
tree = Node 1 [Node 1 [], Node 2 [], Node 3 []]

example1 :: IO ()
example1 = mapM_ print tree

example2 :: Integer
example2 = foldr (+) 0 tree

example3 :: Maybe (Tree Integer)
example3 = traverse (\x -> if x > 2 then Just x else Nothing) tree

example4 :: Tree Integer
example4 = runIdentity $ traverse (\x -> pure (x + 1)) tree
