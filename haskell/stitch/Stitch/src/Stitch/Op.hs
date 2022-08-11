{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
{-# LANGUAGE FlexibleInstances                          #-}
{-# LANGUAGE GADTs                                      #-}
{-# LANGUAGE PatternSynonyms                            #-}
{-# LANGUAGE TypeOperators                              #-}

module  Stitch.Op
  ( pattern UArithOp
  , ArithOp (..)
  , UArithOp
  , arithType
  , eqArithOp
  , eqArithOpB
  , uPlus
  , uMinus
  , uTimes
  , uDivide
  , uMod
  , uLess
  , uLessE
  , uGreater
  , uGreaterE
  , uEquals
  ) where

import Data.Hashable
import Data.Maybe

import Text.PrettyPrint.ANSI.Leijen
import Type.Reflection

import Stitch.Data.Exists
import Stitch.Type ()
import Stitch.Utils

data ArithOp ty where
  Plus      :: ArithOp Int
  Minus     :: ArithOp Int
  Times     :: ArithOp Int
  Divide    :: ArithOp Int
  Mod       :: ArithOp Int
  Less      :: ArithOp Bool
  LessE     :: ArithOp Bool
  Greater   :: ArithOp Bool
  GreaterE  :: ArithOp Bool
  Equals    :: ArithOp Bool

-- | Extract the result type of an Op
arithType :: ArithOp ty -> TypeRep ty
arithType Plus      = typeRep
arithType Minus     = typeRep
arithType Times     = typeRep
arithType Divide    = typeRep
arithType Mod       = typeRep
arithType Less      = typeRep
arithType LessE     = typeRep
arithType Greater   = typeRep
arithType GreaterE  = typeRep
arithType Equals    = typeRep

-- | Existential package for an 'ArithOp'
type UArithOp = SingEx ArithOp

-- | Convenient pattern synonym to hide the underlying representation of UArithOp
pattern UArithOp op = SingEx op
{-# COMPLETE UArithOp #-}

uPlus     :: UArithOp
uMinus    :: UArithOp 
uTimes    :: UArithOp 
uDivide   :: UArithOp 
uMod      :: UArithOp 
uLess     :: UArithOp 
uLessE    :: UArithOp 
uGreater  :: UArithOp 
uGreaterE :: UArithOp 
uEquals   :: UArithOp 

uPlus     =  UArithOp Plus  
uMinus    =  UArithOp Minus    
uTimes    =  UArithOp Times    
uDivide   =  UArithOp Divide   
uMod      =  UArithOp Mod      
uLess     =  UArithOp Less     
uLessE    =  UArithOp LessE    
uGreater  =  UArithOp Greater  
uGreaterE =  UArithOp GreaterE 
uEquals   =  UArithOp Equals   

-- | Compare two 'ArithOp's (potentially of different types) for equality
eqArithOp :: ArithOp ty1 -> ArithOp ty2 -> Maybe (ty1 :~: ty2)
eqArithOp Plus     Plus     = Just Refl
eqArithOp Minus    Minus    = Just Refl
eqArithOp Times    Times    = Just Refl
eqArithOp Divide   Divide   = Just Refl
eqArithOp Mod      Mod      = Just Refl
eqArithOp Less     Less     = Just Refl
eqArithOp LessE    LessE    = Just Refl
eqArithOp Greater  Greater  = Just Refl
eqArithOp GreaterE GreaterE = Just Refl
eqArithOp Equals   Equals   = Just Refl
eqArithOp _        _        = Nothing

-- | Compare two 'ArithOp's for uninformative equality
eqArithOpB :: ArithOp ty1 -> ArithOp ty2 -> Bool
eqArithOpB op1 op2 = isJust (eqArithOp op1 op2)

instance Eq (ArithOp ty) where
  (==) = eqArithOpB

instance Hashable (ArithOp ty) where
  hashWithSalt s op = hashWithSalt s ctor_num
    where
      ctor_num :: Int
      ctor_num = case op of
        Plus     -> 0
        Minus    -> 1
        Times    -> 2
        Divide   -> 3
        Mod      -> 4
        Less     -> 5
        LessE    -> 6
        Greater  -> 7
        GreaterE -> 8
        Equals   -> 9

instance Eq UArithOp where
  UArithOp op1 == UArithOp op2 = op1 `eqArithOpB` op2

instance Pretty (ArithOp ty) where
  pretty Plus     = char '+'
  pretty Minus    = char '-'
  pretty Times    = char '*'
  pretty Divide   = char '/'
  pretty Mod      = char '%'
  pretty Less     = char '<'
  pretty LessE    = text "<="
  pretty Greater  = char '>'
  pretty GreaterE = text ">="
  pretty Equals   = text "=="

instance Show (ArithOp ty) where
  show = render . pretty

instance Pretty UArithOp where
  pretty (UArithOp op) = pretty op

instance Show UArithOp where
  show = render . pretty
