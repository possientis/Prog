{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE KindSignatures         #-}

module Optics.FinVec
    (   check0
    ,   check1
    ,   check2
    ,   check3
    )   where


import Optics.Nat
import Optics.Fin
import Optics.Vec

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

-- Suitable instances of Eq have been defined on 'Vec n a' and
-- 'Fin n -> a'. So we are able to check some equalities.
check0 :: Bool
check0 = vec2Id Nil == (Nil :: Vec 'Z Int) 

check1 :: Bool
check1 = vec2Id (Cons (1 :: Int) (Cons 2 Nil)) == (Cons 1 (Cons 2 Nil))

check2 :: Bool
check2 = fin2Id absurd == absurd 

check3_ :: Fin ('S ('S ('S 'Z)))  -> Int
check3_ FZ = 0
check3_ (FS FZ) = 1
check3_ (FS (FS FZ)) = 2
check3_ (FS (FS (FS _))) = error "should not be called"

check3 :: Bool
check3 = fin2Id check3_ == check3_

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


