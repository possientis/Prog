{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE TypeFamilies   #-}
{-# LANGUAGE TypeInType     #-}
{-# LANGUAGE TypeOperators  #-}

module Stitch.Subst
  ( subst
  ) where

import Data.Kind

import Stitch.Data.Nat
import Stitch.Data.Vec
import Stitch.Exp
import Stitch.Shift

-- | Substitute the first expression into the second. As a proposition,
-- this is the substitution lemma.
subst 
  :: forall ctx s t
   . Exp ctx s 
  -> Exp (s ':> ctx) t 
  -> Exp ctx t
subst = subst_ LZ

subst_ 
  :: forall 
      (m :: Nat)  (locals :: Ctx m)
      (n :: Nat)  (ctx :: Ctx n) 
      (s :: Type) (t :: Type)
   . Length locals
  -> Exp ctx s
  -> Exp (locals :++: s ':> ctx) t
  -> Exp (locals :++: ctx) t
subst_ l e = \case
  (Var v)           -> subst_var l e v
  (Lam ty b)        -> Lam ty (subst_ (LS l) e b)
  (App e1 e2)       -> App (subst_ l e e1) (subst_ l e e2)
  (Let e1 e2)       -> Let (subst_ l e e1) (subst_ (LS l) e e2)
  (Arith e1 op e2)  -> Arith (subst_ l e e1) op (subst_ l e e2)
  (Cond e1 e2 e3)   -> Cond (subst_ l e e1) (subst_ l e e2) (subst_ l e e3)
  (Fix e1)          -> Fix (subst_ l e e1)
  (IntE i)          -> IntE i
  (BoolE b)         -> BoolE b

subst_var
  :: forall 
      (m :: Nat)  (locals :: Ctx m)
      (n :: Nat)  (ctx :: Ctx n) 
      (s :: Type) (t :: Type) 
   . Length locals 
  -> Exp ctx s
  -> Elem (locals :++: s ':> ctx) t
  -> Exp (locals :++: ctx) t
subst_var  LZ    e  EZ    = e 
subst_var  LZ    _ (ES v) = Var v
subst_var (LS _) _  EZ    = Var EZ
subst_var (LS l) e (ES v) = shift (subst_var l e v) 
