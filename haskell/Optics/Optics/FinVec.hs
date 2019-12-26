{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module Optics.FinVec
    (   vec2Id
    ,   fin2Id
    ,   fin2vec'
    )   where


import Optics.Nat
import Optics.Fin
import Optics.Vec
import Optics.Singleton

-- We claim that the types 'Vec n a' and 'Fin n -> a' are isomorphic
vec2fin :: Vec n a -> (Fin n -> a)
vec2fin Nil x = absurd x
vec2fin (Cons v _) FZ = v
vec2fin (Cons _ vs) (FS n') = vec2fin vs n'


-- We cannot define fin2vec directly as we cannot pattern match on
-- values of 'Fin n -> a'. Hence we use a typeclass instead
class Fin2Vec (n :: Nat) where
    fin2vec :: (Fin n -> a) -> Vec n a

instance Fin2Vec 'Z where
    fin2vec _ = Nil 

instance (Fin2Vec n) => Fin2Vec ('S n) where
    fin2vec f = Cons (f FZ) $ fin2vec (\n -> f (FS n))

-- We expect this function to be the identity.
vec2Id :: Fin2Vec n => Vec n a -> Vec n a
vec2Id = fin2vec . vec2fin

-- We expect this function to be the identity
fin2Id :: Fin2Vec n => (Fin n -> a) -> (Fin n -> a)
fin2Id = vec2fin . fin2vec

-- forall n, ... is explicit
fin2vec' :: SNat n -> (Fin n -> a) -> Vec n a
fin2vec' SZ _ = Nil
fin2vec' (SS n) f = Cons (f FZ) $ fin2vec' n (\m -> f (FS m))


{- failing to create a version for 'forall {n}' with implict argument n
fin2vec'' :: forall n a . (SingI n) => (Fin n -> a) -> Vec n a
fin2vec'' f = case (sing @ n) of
    SZ      -> Nil
    (SS _)  -> Cons (f FZ) $ fin2vec'' (\m -> f (FS m))
-}

-- we can also provide pseudo haskell proofs

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

-- fin2Id absurd 
-- = vec2fin (fin2vec absurd)
-- = vec2fin Nil
-- = absurd 
--
-- fin2Id (f :: Fin (S n) -> a) FZ
-- = vec2fin (fin2vec f) FZ
-- = vec2fin (Cons (f FZ) (fin2vec (\n -> f (FS n)))) FZ
-- = f FZ  
--
-- fin2Id (f :: Fin (S n) -> a) (FS n')
-- = vec2fin (fin2vec f) (FS n')
-- = vec2fin (Cons (f FZ) (fin2vec (\n -> f (FS n)))) (FS n')
-- = vec2fin (fin2vec (\n -> f (FS n))) n'
-- = fin2Id (\n -> f (FS n)) n'
-- = (\n -> f (FS n)) n' [induction on n?]
-- = f (FS n')


