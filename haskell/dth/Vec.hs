{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

import Prelude hiding ((+))

data Nat = Zero | Succ Nat

data Vec :: (* -> Nat -> *) where
  Nil   :: Vec a 'Zero
  (:>)  :: a -> Vec a n -> Vec a ('Succ n)

infixr 5 :>


(+) :: Nat -> Nat -> Nat
(+) Zero m      = m
(+) (Succ n) m  = Succ (n + m)

{- doesnt work
append :: Vec a n -> Vec a m -> Vec a (n '+ m)
append Nil w      = w
append (a :> v) w = a :> append v w
-}


listReplicate :: Nat -> a -> [a]
listReplicate Zero      _ = []
listReplicate (Succ n)  x = x : listReplicate n x



