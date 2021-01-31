{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE FunctionalDependencies #-}

module  Pairing
    (   Pairing     (..) 
    ,   move
    )   where

import Control.Comonad

import Data.Functor.Identity

import Store
import State
import Stream
import Sequence

class Pairing f g | f -> g, g -> f where
    pair :: (a -> b -> c) -> f a -> g b -> c

move :: (Comonad w, Pairing m w) => w a -> m b -> w a
move space movement = pair (const id) movement (duplicate space)

instance Pairing Identity Identity where
    pair f (Identity a) (Identity b) = f a b

instance Pairing ((->) a) ((,) a) where
    pair f g (a,b) = f (g a) b 

instance Pairing Sequence Stream where
    pair f (End a) (Cons b _) = f a b
    pair f (Next as) (Cons _ bs) = pair f as bs

instance Pairing (State s) (Store s) where
  pair :: (a -> b -> c) -> State s a -> Store s b -> c
  pair op (State f) (Store g s) = let (a,s') = f s in op a (g s')

_uncurry :: (a -> b -> c) -> (a, b) -> c
_uncurry = pair ($)

s0 :: Stream Integer
s0 = naturals

_s1 :: Stream Integer
_s1 = move s0 (Next (End ()))

_s2 :: Stream Integer
_s2 = move s0 (Next (Next (End ())))

