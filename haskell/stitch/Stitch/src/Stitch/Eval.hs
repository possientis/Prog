{-# LANGUAGE EmptyCase      #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE TypeFamilies   #-}
{-# LANGUAGE TypeInType     #-}
{-# LANGUAGE TypeOperators  #-}

module Stitch.Eval
  ( StepResult  (..)
  , Value
  , ValuePair   (..)
  , eval
  , step
  ) where

import Data.Kind
import Text.PrettyPrint.ANSI.Leijen

import Stitch.Data.Nat
import Stitch.Data.Vec
import Stitch.Exp
import Stitch.Op
import Stitch.Shift

-- | Store a value in both expression form and value form.
data ValuePair ty = ValuePair
  { expr :: Exp 'VNil ty
  , val  :: Value ty
  }

-- | Well-typed closed values.
type family Value t where
  Value Int      = Int
  Value Bool     = Bool
  Value (a -> b) = Exp 'VNil a -> Exp 'VNil b

instance Pretty (ValuePair ty) where
  pretty = pretty . expr

-- | The result of stepping is either a reduction or the detection of a value.
data StepResult :: Type -> Type where
  Step  :: Exp 'VNil ty  -> StepResult ty
  Value :: ValuePair ty  -> StepResult ty

-- | Evaluate an expression, using big-step semantics.
eval :: Exp 'VNil ty -> ValuePair ty
eval = \case
  (Var v)          -> impossibleVar v
  e@(Lam _ b)      -> ValuePair e $ \arg -> subst arg b
  (App e1 e2)      ->  eval (apply (eval e1) (eval e2))
  (Let e1 e2)      ->  eval (subst (expr $ eval e1) e2)
  (Arith e1 op e2) ->  eval (arith (val $ eval e1) op (val $ eval e2))
  (Cond e1 e2 e3)  ->  eval (cond (val $ eval e1) e2 e3)
  (Fix e)          ->  eval (unfix (eval e))
  e@(IntE i)       ->  ValuePair e i
  e@(BoolE b)      ->  ValuePair e b

-- | Step an expression, either to another expression or to a value.
step :: Exp 'VNil ty -> StepResult ty
step = \case
  (Var v)           ->  impossibleVar v

  e@(Lam _ b)       -> Value (ValuePair e $ \ arg -> subst arg b)

  (App e1 e2)       -> 
    case step e1 of
      Step e1'  -> Step (App e1' e2)
      Value fun ->
        case step e2 of
          Step e2'  -> Step (App (expr fun) e2')
          Value arg -> Step (apply fun arg)

  (Let e1 e2)       -> 
    case step e1 of
      Step e1' -> Step (Let e1' e2)
      Value v1 -> Step (subst (expr v1) e2)

  (Arith e1 op e2)  -> case step e1 of
    Step e1' -> Step (Arith e1' op e2)
    Value v1 -> 
      case step e2 of
        Step e2' -> Step (Arith (expr v1) op e2')
        Value v2 -> Step (arith (val v1) op (val v2))

  (Cond e1 e2 e3)   -> case step e1 of
    Step e1' -> Step (Cond e1' e2 e3)
    Value v1 -> Step (cond (val v1) e2 e3)

  (Fix e1)          -> case step e1 of
    Step e1' -> Step (Fix e1')
    Value v1 -> Step (unfix v1)

  e@(IntE n)       -> Value (ValuePair e n)
  e@(BoolE b)      -> Value (ValuePair e b)

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

-- | Given a lambda and an expression, beta-reduce.
apply :: ValuePair (arg -> res) -> ValuePair arg -> Exp 'VNil res
apply fun arg = val fun (expr arg)

-- | Apply an arithmetic operator to two values.
arith :: Int -> ArithOp ty -> Int -> Exp 'VNil ty
arith n1 Plus     n2 = IntE $ n1 + n2
arith n1 Minus    n2 = IntE $ n1 - n2
arith n1 Times    n2 = IntE $ n1 * n2
arith n1 Divide   n2 = IntE $ n1 `div` n2
arith n1 Mod      n2 = IntE $ n1 `mod` n2
arith n1 Less     n2 = BoolE $ n1 < n2
arith n1 LessE    n2 = BoolE $ n1 <= n2
arith n1 Greater  n2 = BoolE $ n1 > n2
arith n1 GreaterE n2 = BoolE $ n1 >= n2
arith n1 Equals   n2 = BoolE $ n1 == n2

-- | Conditionally choose between two expressions
cond :: Bool -> Exp 'VNil t -> Exp 'VNil t -> Exp 'VNil t
cond True  e _ = e
cond False _ e = e

-- | Unroll a `fix` one level
unfix :: ValuePair (ty -> ty) -> Exp 'VNil ty
unfix fix = val fix (Fix . expr $ fix)

-- | A well-typed variable in an empty context is impossible.
impossibleVar :: Elem 'VNil x -> a
impossibleVar = \case {}
