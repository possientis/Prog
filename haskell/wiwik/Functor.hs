{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

import Data.Functor

data Tree a = Node a [Tree a] deriving Show


instance Functor Tree where
  fmap f (Node a ts) = Node (f a) $ map (fmap f) ts


type A = Either String


instance Functor A where
  fmap f (Left s)   = Left s
  fmap f (Right a)  = Right (f a)

type B t = ((->) t)







