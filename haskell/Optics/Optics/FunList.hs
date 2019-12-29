{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ScopedTypeVariables    #-}
module  Optics.FunList
    (   FunList     (..)   
    ,   FunList'    (..)
    ,   FunList_
    ,   e2fun
    ,   fun2e
    ,   nId
    ,   snId
    ,   funId
    ,   fun'Id
    )   where

import Optics.Nat
import Optics.Vec

data FunList a b t = Done t | More a (FunList a b (b -> t))

fun2e :: FunList a b t -> Either t (a, FunList a b (b -> t))
fun2e (Done t)    = Left t
fun2e (More x l)  = Right (x,l) 

e2fun :: Either t (a, FunList a b (b -> t)) -> FunList a b t
e2fun (Left t)        = Done t
e2fun (Right (x,l))   = More x l

-- (e2fun . fun2e) (Done t)   = e2fun (Left t) = Done t
-- (e2fun . fun2e) (More x l) = e2fun (Right (x,l)) = More x l

-- (fun2e . e2fun) (Left t) = fun2e (Done t) = Left t
-- (fun2e . e2fun) (Right (x,l)) = fun2e (More x l) = Right (x,l)


type FunList_ (n :: Nat) a b t = (Vec n a, Vec n b -> t)

-- FunList_ ('S n) a b t and (a, FunList_ n a b (b -> t)) are isomorphic

n2sn :: (a, FunList_ n a b (b -> t)) -> FunList_ ('S n) a b t
n2sn (a, (vec, f)) = (Cons a vec, g) where
    g (Cons b vec') = f vec' b

sn2n :: FunList_ ('S n) a b t -> (a, FunList_ n a b (b -> t))
sn2n (Cons a vec, f) = (a, (vec, g)) where 
    g vec' b = f (Cons b vec')

nId :: (a, FunList_ n a b (b -> t)) -> (a, FunList_ n a b (b -> t))
nId = sn2n . n2sn

snId :: FunList_ ('S n) a b t -> FunList_ ('S n) a b t 
snId = n2sn . sn2n

data FunList' a b t where
     FunList' :: forall (n :: Nat) a b t . FunList_ n a b t -> FunList' a b t


fun2fun' :: FunList a b t -> FunList' a b t
fun2fun' (Done t) = FunList' (Nil, \_ -> t)
fun2fun' (More a fun) = case fun2fun' fun of
   (FunList' (vec,f)) -> FunList' $ n2sn (a , (vec,f))

fun'2fun :: FunList' a b t -> FunList a b t
fun'2fun (FunList' (Nil, f)) = Done (f Nil)
fun'2fun (FunList' (Cons a vec, f)) = case sn2n (Cons a vec, f) of
    (a', (vec', g)) -> More a' (fun'2fun (FunList' (vec', g))) 

funId :: FunList a b t -> FunList a b t 
funId = fun'2fun . fun2fun'

fun'Id :: FunList' a b t -> FunList' a b t 
fun'Id = fun2fun' . fun'2fun

-- pseudo haskell proof

-- funId (Done t) 
-- = (fun'2fun . fun2fun') (Done t)
-- = fun'2fun (fun2fun' (Done t))
-- = fun'2fun (FunList' (Nil, \_ -> t))
-- = Done ((\_ -> t) Nil)
-- = Done t
--
-- funId (More a fun)
-- = (fun'2fun . fun2fun') (More a fun)
-- = fun'2fun (fun2fun' (More a fun))
-- = fun'2fun (FunList' (n2sn (a, (vec, f)))) [FunList' (vec,f) = fun2fun' fun]
-- = fun'2fun (FunList' (Cons a vec, g))      [g (Cons b vec') = f vec' b     ] 
-- = More a' (fun'2fun (FunList' (vec',g')))  
-- where
-- (a', (vec',g')) 
-- = sn2n (Cons a vec, g)
-- = (a, (vec, g'))         [g' vec' b = g (Cons b vec')]    
--

-- nId (a, (vec, f))
-- = (sn2n . n2sn) (a, (vec f))
-- = sn2n (n2sn (a, (vec f)))
-- = sn2n (Cons a vec, g)               [g (Cons b vec') = f vec' b]
-- = (a, (vec, g'))                     [g' vec' b = g (Cons b vec')]
-- = (a, (vec, f))                      [need to show g' = f ]
-- proof of g' = f
-- f :: Vec n b -> b -> t
-- g :: Vec ('S n) n -> t 
-- g':: Vec n b -> b -> t 
-- g' vec' b 
-- = g (Cons b vec')
-- = f vec' b

-- snId (Cons a vec, f)
-- = (n2sn . sn2n) (Cons a vec, f)
-- = n2sn (sn2n (Cons a vec, f))
-- = n2sn (a, (vec , g))        [g vec' b = f (Cons b vec')]
-- = (Cons a vec, g')           [g' (Cons b vec') = g vec' b]
-- = (Cons a vec, f)            [since g' = f :: Vec ('S n) b -> t]

