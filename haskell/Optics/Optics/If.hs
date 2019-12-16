{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE KindSignatures         #-}

module  Optics.If
    (   If
    )   where

type family   If (b :: Bool) (x :: k) (y :: k) :: k
type instance If 'True  x _ = x
type instance If 'False _ y = y
