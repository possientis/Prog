{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ExplicitForAll         #-}

module  Optics.Nat
    (   Nat         (..)
    ,   SNat        (..)
    ,   fromSNat
    )   where

import Data.Kind

data Nat = Z | S Nat

-- SNat 'Z has only one instance
-- SNat ('S 'Z) has only one instance
-- ...
data SNat (n :: Nat) :: Type where
    SZ :: SNat 'Z
    SS :: forall (n :: Nat) . SNat n -> SNat ('S n)

fromSNat :: SNat n -> Nat
fromSNat SZ     = Z
fromSNat (SS n) = S (fromSNat n)




