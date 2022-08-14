{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}

module  Stitch.Shift
  ( Shiftable (..)
  , shift
  , uncheckedUnshift
  , unshift
  ) where

import Data.Kind
--import Unsafe.Coerce

import Stitch.Data.Nat
import Stitch.Data.Vec
import Stitch.Exp

-- | Kind of 'Exp' and 'Elem'
type ShiftableKind = forall (n :: Nat) . Ctx n -> Type -> Type

class Shiftable (a :: ShiftableKind) where
  -- | Shift all de Bruijn indices to accommodate a new context prefix
  shifts   :: Length prefix -> a ctx ty -> a (prefix :++: ctx) ty

  -- | Shift a closed term into a context with bound variables; this
  -- can often be more efficient than the general case
  shifts0  :: a 'VNil ty -> a prefix ty

  -- | Lower de Bruijn indices if possible; fails if an index is too low
  unshifts :: Length prefix -> a (prefix :++: ctx) ty -> Maybe (a ctx ty)

-- | Convenient abbreviation for the common case of shifting by only one index
shift 
  :: forall (a :: ShiftableKind)(n :: Nat)(ctx :: Ctx n)(t :: Type)(ty :: Type)
   . Shiftable a 
  => a ctx ty 
  -> a (t ':> ctx) ty
shift = shifts (LS LZ)

-- | Convenient synonym for the common case of unshifting by only one level.
unshift 
  :: forall (a :: ShiftableKind)(n :: Nat)(ctx :: Ctx n)(t :: Type)(ty :: Type)
   . Shiftable a 
  => a (t ':> ctx) ty 
  -> Maybe (a ctx ty)
unshift = unshifts (LS LZ)

-- | Unshift, but assert that this succeeds
uncheckedUnshift 
  :: forall (a :: ShiftableKind)(n :: Nat)(ctx :: Ctx n)(t :: Type)(ty :: Type)
   . Shiftable a 
  => a (t ':> ctx) ty 
  -> a ctx ty
uncheckedUnshift e = case unshift e of
  Just e' -> e'
  Nothing -> error "uncheckedUnshift failure"

instance Shiftable Exp where
  shifts    = shiftsExp
  shifts0   = shifts0Exp
  unshifts  = unshiftsExp


instance Shiftable Elem where
  shifts    = weakenElem
  shifts0   = \case {}
  unshifts  = strengthenElem

-- | Convert an expression typed in one context to one typed in a larger
-- context. Operationally, this amounts to de Bruijn index shifting.
-- As a proposition, this is the weakening lemma.
shiftsExp 
  :: forall (n :: Nat) (m :: Nat) (prefix :: Ctx n) (ctx :: Ctx m) (ty :: Type)
   . Length prefix 
  -> Exp ctx ty 
  -> Exp (prefix :++: ctx) ty
shiftsExp preLen = go LZ
  where
    go :: forall (p :: Nat) (locals :: Ctx p) (t :: Type) 
        . Length locals
       -> Exp (locals :++: ctx) t 
       -> Exp (locals :++: prefix :++: ctx) t
    go len (Var v)          = Var (shifts_var len v)
    go len (Lam ty body)    = Lam ty (go (LS len) body)
    go len (App e1 e2)      = App (go len e1) (go len e2)
    go len (Let e1 e2)      = Let (go len e1) (go (LS len) e2)
    go len (Arith e1 op e2) = Arith (go len e1) op (go len e2)
    go len (Cond e1 e2 e3)  = Cond (go len e1) (go len e2) (go len e3)
    go len (Fix e)          = Fix (go len e)
    go _   (IntE i)         = IntE i
    go _   (BoolE b)        = BoolE b

    shifts_var 
      :: forall (p :: Nat) (locals :: Ctx p) (t :: Type) 
       . Length (locals)
      -> Elem (locals :++: ctx) t
      -> Elem (locals :++: prefix :++: ctx) t
    shifts_var LZ     v      = weakenElem preLen v
    shifts_var (LS _) EZ     = EZ
    shifts_var (LS l) (ES e) = ES (shifts_var l e)


-- | If an expression is closed, we actually have no work to do. Unfortunately,
-- we cannot convince GHC of this fact, and so we have to recur out to the leaves
-- to fix the types.
shifts0Exp 
  :: forall (n :: Nat) (prefix :: Ctx n) (ty :: Type)
   . Exp 'VNil ty 
  -> Exp prefix ty
shifts0Exp = go LZ
  where
    go :: forall (p :: Nat) (locals :: Ctx p) (t :: Type) 
        . Length locals 
       -> Exp locals t 
       -> Exp (locals :++: prefix) t
    go len (Var v)          = Var (shifts0_var v len)
    go len (Lam ty body)    = Lam ty (go (LS len) body)
    go len (App e1 e2)      = App (go len e1) (go len e2)
    go len (Let e1 e2)      = Let (go len e1) (go (LS len) e2)
    go len (Arith e1 op e2) = Arith (go len e1) op (go len e2)
    go len (Cond e1 e2 e3)  = Cond (go len e1) (go len e2) (go len e3)
    go len (Fix e)          = Fix (go len e)
    go _   (IntE n)         = IntE n
    go _   (BoolE b)        = BoolE b

    shifts0_var 
      :: forall (p :: Nat) (locals :: Ctx p) (t :: Type) 
       . Elem locals t
      -> Length locals 
      -> Elem (locals :++: prefix) t
    shifts0_var EZ     _        = EZ
    shifts0_var (ES v) (LS len) = ES (shifts0_var v len)

{-
-- Because shifts0Exp provably does nothing, let's just short-circuit it:
{-# NOINLINE shifts0Exp #-}
{-# RULES "shifts0Exp" shifts0Exp = unsafeCoerce #-}
-}

-- | Unshift an expression. This is essentially a strengthening lemma, which fails
-- precisely when de Bruijn index of a free variable to be unshifted is too low.
unshiftsExp 
  :: forall prefix ctx ty
   . Length prefix 
  -> Exp (prefix :++: ctx) ty 
  -> Maybe (Exp ctx ty)
unshiftsExp prefix = go LZ
  where
    go :: forall num_locals (locals :: Ctx num_locals) t
        . Length locals
       -> Exp (locals :++: prefix :++: ctx) t
       -> Maybe (Exp (locals :++: ctx) t)
    go len (Var v)          = Var <$> unshift_var len v
    go len (Lam ty body)    = Lam ty <$> go (LS len) body
    go len (App e1 e2)      = App <$> go len e1 <*> go len e2
    go len (Let e1 e2)      = Let <$> go len e1 <*> go (LS len) e2
    go len (Arith e1 op e2) = Arith <$> go len e1 <*> pure op <*> go len e2
    go len (Cond e1 e2 e3)  = Cond <$> go len e1 <*> go len e2 <*> go len e3
    go len (Fix e)          = Fix <$> go len e
    go _   (IntE n)         = pure (IntE n)
    go _   (BoolE b)        = pure (BoolE b)

    unshift_var 
      :: forall num_locals (locals :: Ctx num_locals) t
       . Length locals
      -> Elem (locals :++: prefix :++: ctx) t
      -> Maybe (Elem (locals :++: ctx) t)
    unshift_var LZ       v      = strengthenElem prefix v
    unshift_var (LS _)   EZ     = pure EZ
    unshift_var (LS len) (ES v) = ES <$> unshift_var len v
