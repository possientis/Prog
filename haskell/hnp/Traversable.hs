{-# Language StandaloneDeriving #-}
{-# Language DeriveTraversable #-}

import Data.Traversable
import Data.Monoid ((<>), mempty)

data Tree a = Leaf | Node (Tree a) a (Tree a)

myTree :: Tree Char
myTree = Node (Node Leaf 'a' Leaf) 'b' (Node Leaf 'c' Leaf)

instance Functor Tree where
    fmap f Leaf = Leaf
    fmap f (Node l v r) = Node (fmap f l) (f v) (fmap f r)


instance Foldable Tree where
    foldMap f Leaf = mempty
    foldMap f (Node l v r) = foldMap f l <> f v <> foldMap f r


--deriving instance Traversable Tree


instance Traversable Tree where
    sequenceA Leaf = pure Leaf
    sequenceA (Node l v r) = Node <$> sequenceA l <*> v <*> sequenceA r

{-

class (Functor t, Foldable t) => Traversable t where
{-# MINIMAL traverse | sequenceA #-}

traverse :: Applicative f => (a -> f b) -> t a -> f (t b) 
traverse f = sequenceA . fmap f

sequenceA :: Applicative f => t (f a) -> f (t a)
sequenceA = traverse id

-}

main :: IO ()
main = do
    _ <- traverse print myTree
    return ()


