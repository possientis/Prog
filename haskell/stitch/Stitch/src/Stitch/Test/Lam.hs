{-# LANGUAGE TypeInType     #-}

module Stitch.Test.Lam
  ( Exp (..)
  ) where

import Stitch.Data.Fin
import Stitch.Data.Nat

-- | de Bruijn terms for untyped lambda calculus
data Exp (n :: Nat) 
  = Var (Fin n)
  | Lam (Exp ('Succ n))
  | App (Exp n) (Exp n)

_0 :: Exp ('Succ n)
_0 = Var FZ 

_1 :: Exp ('Succ ('Succ n))
_1 = Var (FS FZ)

_2 :: Exp ('Succ ('Succ ('Succ n)))
_2 = Var (FS (FS FZ))

_3 :: Exp ('Succ ('Succ ('Succ ('Succ n))))
_3 = Var (FS (FS (FS FZ)))

-- Church zero
-- c0 = Lam s . Lam z . z
_c0 :: Exp 'Zero
_c0 = Lam (Lam _0)

-- Church 2
-- c2 = Lam s . Lam z . s (s z)
_c2 :: Exp 'Zero
_c2 = Lam (Lam (App _1 (App _1 _0)))

-- Church addition
-- plus = Lam m . Lam n . Lam s . Lam z . m s (n s z)
_plus :: Exp 'Zero
_plus = Lam (Lam (Lam (Lam (App (App _3 _1) (App (App _2 _1) _0)))))
