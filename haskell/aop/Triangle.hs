{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module  Triangle
    (   triangle1
    ,   triangle2
    ,   triangle3 
    ,   triangle4
    )   where

import Data.Bifunctor
import Data.Functor.Foldable

triangle1 :: (a -> a) -> [a] -> [a]
triangle1 f = \case
    []   -> []
    x:xs -> x:map f (triangle1 f xs)

triangle2 :: (a -> a) -> [a] -> [a]
triangle2 f = cata $ \case
    Nil         -> []
    Cons x xs   -> x : map f xs

triangle3_ :: (a -> a) -> ListF a [a] -> [a]
triangle3_ f = \case
    Nil         -> []
    Cons x xs   -> x : map f xs

triangle3 :: (a -> a) -> [a] -> [a]
triangle3 = cata . triangle3_

-- initial type of bifunctor ListF
mu4 :: forall a . ListF a [a] -> [a]
mu4 = \case
    Nil         -> []
    Cons x xs   -> x : xs

triangle4_ :: (a -> a) -> ListF a [a] -> [a]
triangle4_ f = mu4 . bimap id (map f) 

triangle4 :: (a -> a) -> [a] -> [a]
triangle4 = cata . triangle4_




