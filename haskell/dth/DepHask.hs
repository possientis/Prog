{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

module  DepHask
    (   Nat (..)
    ,   Vec (..)
    ,   (:~:)
    ,   HList (..)
    ,   (+)
    )   where

import Prelude hiding ((+), pred)

data Nat = Zero | Succ Nat

data Vec :: * -> Nat -> * where
    Nil   :: Vec a 'Zero
    (:>)  :: a -> Vec a n -> Vec a ('Succ n)

infixr 5 :>

data a :~: b where
    Refl :: a :~: a

data HList :: [*] -> * where
    HNil  :: HList '[]
    (:::) :: h -> HList t -> HList (h ': t)

infix 5 :::

(+) :: Nat -> Nat -> Nat
Zero + m    = m
Succ n + m  = Succ (n + m)

-- This fails to compile
-- (+) promoted at type level with '
{-
append :: Vec a n -> Vec a m -> Vec a (n '+ m)
append Nil v        = v
append (h :> t) v   = h :> (append t v)
-}


pred :: Nat -> Nat
pred Zero       = error "pred Zero"
pred (Succ n)   = n

{-
safeTail :: Vec a n -> Either (n :~: 'Zero) (Vec a ('pred n))
safeTail = undefined
-}
