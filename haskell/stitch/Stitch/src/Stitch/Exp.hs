{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# OPTIONS_GHC -Wno-orphans      #-}  -- Hashable instance for Elem

module  Stitch.Exp
  ( Ctx
  , Exp           (..)
  , KnownLength
  , eqExp
  , eqExpB
  , exprType
  ) where

import Data.Hashable
import Data.Kind
import Data.Maybe
import Data.Type.Equality

import Text.PrettyPrint.ANSI.Leijen

import Type.Reflection            hiding (App)

import Stitch.Data.IHashable
import Stitch.Data.Nat
import Stitch.Data.Singletons
import Stitch.Data.Vec

import Stitch.Op
import Stitch.Pretty
import Stitch.Type
import Stitch.Utils

-- | A context is just a vector of types
type Ctx = Vec Type

-- | Convenient constraint synonym
type KnownLength (ctx :: Ctx n) = SingI n

-- | @Exp ctx ty@ is a well-typed expression of type @ty@ in context
-- @ctx@. Note that a context is a list of types, where a type's index
-- in the list indicates the de Bruijn index of the associated term-level
-- variable.
data Exp :: forall (n :: Nat) . Ctx n -> Type -> Type where
  Var   :: Elem ctx ty -> Exp ctx ty
  Lam   :: TypeRep arg -> Exp (arg ':> ctx) res -> Exp ctx (arg -> res)
  App   :: Exp ctx (arg -> res) -> Exp ctx arg -> Exp ctx res
  Let   :: Exp ctx rhs_ty -> Exp (rhs_ty ':> ctx) body_ty -> Exp ctx body_ty
  Arith :: Exp ctx Int -> ArithOp ty -> Exp ctx Int -> Exp ctx ty
  Cond  :: Exp ctx Bool -> Exp ctx ty -> Exp ctx ty -> Exp ctx ty
  Fix   :: Exp ctx (ty -> ty) -> Exp ctx ty
  IntE  :: Int -> Exp ctx Int
  BoolE :: Bool -> Exp ctx Bool

deriving instance Show (Exp ctx ty)

-- | Informative equality on expressions
eqExp 
  :: forall (n :: Nat) (ctx :: Ctx n) (ty1 :: Type) (ty2 :: Type)
   . Exp ctx ty1 
  -> Exp ctx ty2 
  -> Maybe (ty1 :~: ty2)

eqExp (Var v1) (Var v2) = eqElem v1 v2

eqExp (Lam t1 b1) (Lam t2 b2) = do 
  HRefl <- eqTypeRep t1 t2
  Refl  <- eqExp b1 b2
  return Refl

eqExp (App f1 a1) (App f2 a2) = do 
  Refl <- eqExp f1 f2
  Refl <- eqExp a1 a2
  return Refl

eqExp (Let e1 b1) (Let e2 b2) = do 
  Refl <- eqExp e1 e2
  Refl <- eqExp b1 b2
  return Refl

eqExp (Arith l1 op1 r1) (Arith l2 op2 r2) = do 
  Refl <- eqExp l1 l2
  Refl <- eqArithOp op1 op2
  Refl <- eqExp r1 r2
  return Refl

eqExp (Cond c1 t1 f1) (Cond c2 t2 f2) = do 
  Refl <- eqExp c1 c2
  Refl <- eqExp t1 t2
  Refl <- eqExp f1 f2
  return Refl

eqExp (Fix b1) (Fix b2) = do 
  Refl <- eqExp b1 b2
  return Refl

eqExp (IntE i1) (IntE i2) 
  | i1 == i2  = Just Refl
  | otherwise = Nothing

eqExp (BoolE b1) (BoolE b2) 
  | b1 == b2  = Just Refl
  | otherwise = Nothing

eqExp _ _ = Nothing

instance TestEquality (Exp ctx) where
  testEquality = eqExp

instance KnownLength ctx => Hashable (Exp ctx ty) where
  hashWithSalt s = \case
    (Var v)           -> hashDeBruijn s v sing
    (Lam t b)         -> s `hashWithSalt` t `hashWithSalt` b
    (App f a)         -> s `hashWithSalt` f `hashWithSalt` a
    (Let e b)         -> s `hashWithSalt` e `hashWithSalt` b
    (Arith l op r)    -> s `hashWithSalt` l `hashWithSalt` op `hashWithSalt` r
    (Cond c t f)      -> s `hashWithSalt` c `hashWithSalt` t  `hashWithSalt` f
    (Fix b)           -> s `hashWithSalt` b
    (IntE i)          -> s `hashWithSalt` i
    (BoolE b)         -> s `hashWithSalt` b

instance KnownLength ctx => IHashable (Exp ctx) where
  ihashWithSalt = hashWithSalt
  ihash = hash

instance KnownLength ctx => Hashable (Elem ctx ty) where
  hashWithSalt s v = hashDeBruijn s v sing

-- | The identity of a de Bruijn index comes from the difference 
-- between the size of the context and the value of the index. We 
-- use this when hashing so that, say, (#2 #3) is recognized as 
-- the same expression as the body of λ.(#3 #4).
hashDeBruijn 
  :: forall (n :: Nat) (ctx :: Ctx n) (ty :: Type)
   . Int 
  -> Elem ctx ty
  -> SNat n 
  -> Int
hashDeBruijn s EZ     sn         = hashWithSalt s (snatToInt sn)
hashDeBruijn s (ES e) (SSucc sn) = hashDeBruijn s e sn

-- | Equality on expressions, needed for testing.
--   Original definition not defined in terms of eqExp, not sure why
eqExpB 
  :: forall (n :: Nat) (ctx :: Ctx n) (ty1 :: Type) (ty2 :: Type)
   . Exp ctx ty1 
  -> Exp ctx ty2 
  -> Bool
eqExpB e1 e2 = isJust $ eqExp e1 e2

-- | Extract the type of an expression
exprType :: SVec ctx -> Exp ctx ty -> TypeRep ty
exprType ctx (Var v)        = elemToSing v ctx
exprType ctx (Lam t b)      = Fun t $ exprType (t :%> ctx) b
exprType ctx (App f _)      = extractResType (exprType ctx f)
exprType ctx (Let e b)      = exprType (exprType ctx e :%> ctx) b
exprType _   (Arith _ op _) = arithType op
exprType ctx (Cond _ t _)   = exprType ctx t
exprType ctx (Fix b)        = extractResType (exprType ctx b)
exprType _   (IntE _)       = typeRep
exprType _   (BoolE _)      = typeRep


----------------------------------------------------
-- Pretty-printing

instance Pretty (Exp 'VNil ty) where
  pretty = prettyExp topPrec

instance 
  forall (n :: Nat) (ctx :: Ctx n) ty
   . SingI n 
  => PrettyExp (Exp ctx ty) 

  where
    type NumBoundVars (Exp ctx ty) = n
    prettyExp = pretty_exp

pretty_exp :: SingI n => Precedence -> Exp (ctx :: Ctx n) ty -> Doc
pretty_exp _    (Var v)          = prettyVar (elemToFin v)
pretty_exp prec (Lam t b)        = prettyLam prec t b
pretty_exp prec (App f a)        = prettyApp prec f a
pretty_exp prec (Let e b)        = prettyLet prec e b
pretty_exp prec (Arith l op r)   = prettyArith prec l op r
pretty_exp prec (Cond c t f)     = prettyIf prec c t f
pretty_exp prec (Fix b)          = prettyFix prec b
pretty_exp _    (IntE i)         = int i
pretty_exp _    (BoolE True)     = text "true"
pretty_exp _    (BoolE False)    = text "false"

-- (\x:Int. x + 1) 5
_test1 :: Exp 'VNil Int
_test1 = App (Lam (typeRep @Int) (Arith (Var EZ) Plus (IntE 1))) (IntE 5)
