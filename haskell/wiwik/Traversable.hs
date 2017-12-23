{-# LANGUAGE NoImplicitPrelude #-}

import Data.Functor
import Data.Foldable
import Data.Monoid

import Control.Applicative

class (Functor t, Foldable t) => Traversable t where
    traverse :: Applicative f => (a -> f b) -> t a -> f (t b)


newtype Identity a = Identity a

instance Functor Identity where
    fmap f (Identity x) = Identity (f x)

instance Applicative Identity where
    pure  = Identity
    Identity f <*> Identity x = Identity (f x)

newtype Compose f g a = Compose (f (g a))

instance (Functor f, Functor g) => Functor (Compose f g) where
    fmap f (Compose x) = Compose (fmap (fmap f) x)

instance (Applicative f, Applicative g) => Applicative (Compose f g) where
    pure x = Compose (pure (pure x))
    Compose f <*> Compose x = Compose (fmap (<*>) f <*> x)


data Tree a = Empty | Leaf a | Node (Tree a) a (Tree a)

instance Functor Tree where
    fmap f Empty    = Empty 
    fmap f (Leaf x) = Leaf (f x)
    fmap f (Node l x r) = Node (fmap f l) (f x) (fmap f r)

instance Foldable Tree where
    foldMap f Empty         = mempty
    foldMap f (Leaf x)      = f x
    foldMap f (Node l x r)  = foldMap f l `mappend` f x `mappend` foldMap f r

instance Traversable Tree where
    traverse f Empty        = pure Empty 
    traverse f (Leaf x)     = pure Leaf <*> f x  
    traverse f (Node l x r) = pure Node <*> traverse f l <*> f x <*> traverse f r 
    







