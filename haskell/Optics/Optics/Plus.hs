{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeFamilies           #-}

module  Optics.Plus
    (   Plus
    ,   plus
    ,   sPlus
    )   where


import Optics.Nat

-- term level
plus :: Nat -> Nat -> Nat
plus  Z    m = m
plus (S n) m = S (plus n m)

-- type level
type family Plus (n :: Nat) (m :: Nat) :: Nat where
    Plus  'Z    m = m
    Plus ('S n) m = 'S (Plus n m)

-- singleton level
sPlus :: SNat n -> SNat m -> SNat (Plus n m)
sPlus  SZ    m = m
sPlus (SS n) m = SS (sPlus n m) 
