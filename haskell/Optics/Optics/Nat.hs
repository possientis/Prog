{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ExplicitForAll         #-}

module  Optics.Nat
    (   Nat         (..)
    ,   SNat        (..)
    ,   fromSNat
    )   where

import Prelude      hiding (toInteger)
import Data.Kind

data Nat = Z | S Nat
    deriving (Eq)

toInteger :: Nat -> Integer
toInteger Z = 0
toInteger (S n) = 1 + toInteger n

instance Show Nat where
    show = show . toInteger

-- SNat 'Z has only one instance
-- SNat ('S 'Z) has only one instance
-- ...
data SNat (n :: Nat) :: Type where
    SZ :: SNat 'Z
    SS :: forall (n :: Nat) . SNat n -> SNat ('S n)

fromSNat :: SNat n -> Nat
fromSNat SZ     = Z
fromSNat (SS n) = S (fromSNat n)

instance Eq (SNat n) where
    (==) _ _ = True     -- singleton type

instance Show (SNat n) where
    show = show . fromSNat

