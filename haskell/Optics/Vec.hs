{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ExplicitForAll         #-}

module  Optics.Vec
    (   Vec (..)
    ,   vec2fin
    ,   fin2vec
    )   where

import Data.Kind
import Optics.Nat
import Optics.Fin

data Vec (n :: Nat) (a :: Type) :: Type where
    Nil  :: forall (a :: Type) . Vec 'Z a
    Cons :: forall (a :: Type) (n :: Nat) . a -> Vec n a -> Vec ('S n) a

vec2fin :: Vec n a -> (Fin n -> a)
vec2fin Nil x = absurd x
vec2fin (Cons v _) FZ = v
vec2fin (Cons _ vs) (FS n') = vec2fin vs n'

class Fin2Vec (n :: Nat) where
    fin2vec :: (Fin n -> a) -> Vec n a

instance Fin2Vec 'Z where
    fin2vec _ = Nil 

instance (Fin2Vec n) => Fin2Vec ('S n) where
    fin2vec f = Cons (f FZ) $ fin2vec (\n -> f (FS n))


