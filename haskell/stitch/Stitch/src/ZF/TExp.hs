{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE ExplicitForAll       #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}

module ZF.TExp
  ( Ctx
  , KnownLength
  , TExp (..)
  ) where

import Data.Kind

import Stitch.Data.Nat
import Stitch.Data.Vec
import Stitch.Data.Singletons

import ZF.Sort

type Ctx = Vec Sort

-- | Convenient constraint synonym
type KnownLength (ctx :: Ctx n) = SingI n

-- | Expressions for types, indexed by context and sort.
-- Var: variables which can be of any sort (Prop, Set and function sorts)
-- Lam: Lambda abstraction
-- App: function Application
-- Let: Let expression, convenience, need not be a primitive
-- Bot: Type expression of sort Prop, signifying bottom, absurd, False
-- In : Type expression of sort Prop, signifying that a set is element of another
-- Imp: Type expression of sort Prop, signifing that a prop implies another
-- All: Quantification of a proposition over a Set variable
-- The: Creating **The** set which satisfies a given predicate.
--
-- The constructor 'The' may seem surprising as given a predicate (a type 
-- expression of sort Prop with at least one free variable), the existence
-- of a 'set satisfying the predicate' may arise wihout uniqueness or may
-- even be provably false. It should be remembered that '**The** set which
-- satisfies the given predicate' is only meant to provide a reasonable
-- intuition. The exact meaning of 'The' will be derived from formal semantic
-- rules such as (given predicates P and Q)
--
-- P (The x. Q x) ~~> All y. Q y => P y
--
-- In other words, when we say that the set 'The x. Q x' satisfies the
-- predicate P, what we are really saying is that any set satisfying the 
-- predicate Q also satisfies P.

data TExp :: forall (n :: Nat) . Ctx n -> Sort -> Type where
  Var :: Elem ctx srt -> TExp ctx srt
  Lam :: SSort arg -> TExp (arg ':> ctx) res -> TExp ctx (arg ':->: res)
  App :: TExp ctx (arg ':->: res) -> TExp ctx arg -> TExp ctx res
  Let :: TExp ctx rhs -> TExp (rhs ':> ctx) res -> TExp ctx res
  Bot :: TExp ctx 'Prop
  In  :: TExp ctx 'Set -> TExp ctx 'Set -> TExp ctx 'Prop
  Imp :: TExp ctx 'Prop  -> TExp ctx 'Prop  -> TExp ctx 'Prop 
  All :: TExp ('Set ':> ctx) 'Prop -> TExp ctx 'Prop
  The :: TExp ('Set ':> ctx) 'Prop -> TExp ctx 'Set

