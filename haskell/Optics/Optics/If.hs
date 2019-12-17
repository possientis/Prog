{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE KindSignatures         #-}

module  Optics.If
    (   If
    ,   sIf
    )   where

import Optics.Nat
import Optics.Bool

-- term level
-- if b then x else y

-- type level
type family   If (b :: Bool) (n :: Nat) (m :: Nat) :: Nat where
    If 'True  x _ = x
    If 'False _ y = y

-- singleton level
sIf :: SBool b -> SNat n -> SNat m -> SNat (If b n m) 
sIf STrue  n _ = n  
sIf SFalse _ m = m
