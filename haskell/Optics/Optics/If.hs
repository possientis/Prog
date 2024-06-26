{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE KindSignatures         #-}

module  Optics.If
    (   If
    ,   sIf
    )   where

import Optics.Singleton

-- term level
-- if b then x else y

-- type level
type family   If (b :: Bool) (n :: k) (m :: k) :: k where
    If 'True  x _ = x
    If 'False _ y = y

-- singleton level (for kind Nat)
sIf :: SBool b -> SNat n -> SNat m -> SNat (If b n m) 
sIf STrue  n _ = n  
sIf SFalse _ m = m
