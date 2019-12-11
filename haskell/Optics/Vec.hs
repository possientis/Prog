{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ExplicitForAll         #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module  Optics.Vec
    (   Vec (..)
    ,   vec2fin
    ,   fin2vec
    ,   main
    )   where

import Data.Kind
import Optics.Nat
import Optics.Fin

data Vec (n :: Nat) (a :: Type) :: Type where
    Nil  :: forall (a :: Type) . Vec 'Z a
    Cons :: forall (a :: Type) (n :: Nat) . a -> Vec n a -> Vec ('S n) a

instance (Eq a) => Eq (Vec n a) where
    (==) Nil Nil = True
    (==) (Cons x xs) (Cons y ys) = (x == y) && xs == ys

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

vec2Id :: Fin2Vec n => Vec n a -> Vec n a
vec2Id = fin2vec . vec2fin

fin2Id :: Fin2Vec n => (Fin n -> a) -> (Fin n -> a)
fin2Id = vec2fin . fin2vec

-- vec2Id Nil 
-- = (fin2vec . vec2fin) Nil
-- = fin2vec (vec2fin Nil)
-- = fin2vec absurd    
-- = Nil (n = 'Z) 

-- vec2Id (Cons x xs) 
-- = (fin2vec . vec2fin) (Cons x xs)
-- = fin2vec (vec2fin (Cons x xs))
-- = Cons (f FZ) $ fin2vec (\n -> f (FS n)) [f = vec2fin (Cons x xs)]
-- = Cons x $ fin2vec (\n -> vec2fin xs n)
-- = Cons x $ fin2vec (vec2fin xs)
-- = Cons x $ vecId xs
-- = Cons x xs [induction on n?]


check0 :: Bool
check0 = vec2Id Nil == (Nil :: Vec 'Z Int) 

check1 :: Bool
check1 = vec2Id (Cons (1 :: Int) (Cons 2 Nil)) == (Cons 1 (Cons 2 Nil))

main :: IO ()
main = do
    print check0
    print check1

