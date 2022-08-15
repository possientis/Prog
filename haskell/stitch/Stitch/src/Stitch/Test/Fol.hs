{-# LANGUAGE TypeInType     #-}

module Stitch.Test.Fol
  ( Exp (..)
  ) where

import Stitch.Data.Fin
import Stitch.Data.Nat

-- | de Bruijn terms for Fol
data Exp (n :: Nat) 
  = Bot
  | In (Fin n) (Fin n)
  | Imp (Exp n) (Exp n)
  | All (Exp ('Succ n))

_0 :: Fin ('Succ n)
_0 = FZ

_1 :: Fin ('Succ ('Succ n))
_1 = FS FZ

-- bottom
_bot :: Exp 'Zero
_bot = Bot

-- x : x
_t1 :: Exp ('Succ 'Zero)
_t1 = In _0 _0

-- x : y
_t2 :: Exp ('Succ ('Succ 'Zero))
_t2 = In _0 _1

_t3 :: Exp ('Succ ('Succ 'Zero))
_t3 = In _1 _0

-- forall x y . x : y
_t4 :: Exp 'Zero
_t4 = All (All (In _1 _0))

-- forall x y . y : x
_t5 :: Exp 'Zero
_t5 = All (All (In _0 _1))

