{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
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

import Data.Maybe
import Type.Reflection

import Stitch.Data.Exists
import Stitch.Type ()

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

