{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ScopedTypeVariables    #-}
module  Optics.FunList
    (   FunList     (..)   
    ,   FunList_
    ,   inn
    ,   out
    ,   n_to_n
    ,   sn_to_sn
    )   where

import Optics.Nat
import Optics.Vec

data FunList a b t = Done t | More a (FunList a b (b -> t))

out :: FunList a b t -> Either t (a, FunList a b (b -> t))
out (Done t)    = Left t
out (More x l)  = Right (x,l) 

inn :: Either t (a, FunList a b (b -> t)) -> FunList a b t
inn (Left t)        = Done t
inn (Right (x,l))   = More x l

-- (inn . out) (Done t)   = inn (Left t) = Done t
-- (inn . out) (More x l) = inn (Right (x,l)) = More x l

-- (out . inn) (Left t) = out (Done t) = Left t
-- (out . inn) (Right (x,l)) = out (More x l) = Right (x,l)


type FunList_ (n :: Nat) a b t = (Vec n a, Vec n b -> t)

-- FunList_ ('S n) a b t and (a, FunList_ n a b (b -> t)) are isomorphic

n_to_sn :: (a, FunList_ n a b (b -> t)) -> FunList_ ('S n) a b t
n_to_sn (a, (vec, f)) = (Cons a vec, g) where
    g (Cons b vec') = f vec' b

sn_to_n :: FunList_ ('S n) a b t -> (a, FunList_ n a b (b -> t))
sn_to_n (Cons a vec, f) = (a, (vec, g)) where 
    g vec' b = f (Cons b vec')

n_to_n :: (a, FunList_ n a b (b -> t)) -> (a, FunList_ n a b (b -> t))
n_to_n = sn_to_n . n_to_sn

sn_to_sn :: FunList_ ('S n) a b t -> FunList_ ('S n) a b t 
sn_to_sn = n_to_sn . sn_to_n

-- pseudo haskell proof

-- n_to_n (a, (vec, f))
-- = (sn_to_n . n_to_sn) (a, (vec f))
-- = sn_to_n (n_to_sn (a, (vec f)))
-- = sn_to_n (Cons a vec, g)            [g (Cons b vec') = f vec' b]
-- = (a, (vec, g'))                     [g' vec' b = g (Cons b vec')]
-- = (a, (vec, f))                      [need to show g' = f ]
-- proof of g' = f
-- f :: Vec n b -> b -> t
-- g :: Vec ('S n) n -> t 
-- g':: Vec n b -> b -> t 
-- g' vec' b 
-- = g (Cons b vec')
-- = f vec' b

--TODO
