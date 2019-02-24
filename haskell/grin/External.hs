{-# LANGUAGE OverloadedStrings #-}

module  External
    (   External (..) 
    ,   add64
    ,   mul64
    )   where

import Name
import SimpleType

data External
    = External
    { eName         :: Name
    , eRetType      :: Ty
    , eArgsType     :: [Ty]
    , eEffectful    :: Bool
    }

data Ty
    = TyCon Name [Ty]
    | TyVar Name
    | TySimple SimpleType
    deriving (Eq, Ord, Show)

int64 :: Ty
int64  = TySimple T_Int64

add64 :: External
add64  = External 
    { eName      = NM "add64"
    , eRetType   = int64
    , eArgsType  = [int64, int64]
    , eEffectful = False
    }  

mul64 :: External
mul64  = External 
    { eName      = NM "mul64"
    , eRetType   = int64
    , eArgsType  = [int64, int64]
    , eEffectful = False
    }  



