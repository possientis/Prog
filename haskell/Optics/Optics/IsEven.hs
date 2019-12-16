{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}

module  Optics.IsEven
    (   IsEven
    ,   isEven
    ,   sIsEven
    )   where



import Optics.Nat


-- term level
isEven :: Nat -> Bool 
isEven Z = True
isEven (S Z) = False
isEven (S (S n)) = isEven n

-- type level
type family   IsEven (n :: Nat) :: Bool
type instance IsEven  'Z = 'True
type instance IsEven ('S 'Z) = 'False 
type instance IsEven ('S ('S n)) = IsEven n

-- singleton level
sIsEven :: SNat n -> SBool (IsEven n)
sIsEven SZ = STrue
sIsEven (SS SZ) = SFalse
sIsEven (SS (SS n)) = sIsEven n

-- term level
nextEven :: Nat -> Nat 
nextEven n = if isEven n then n else S n 

-- type level
type family   NextEven (n :: Nat) :: Nat
type instance NextEven n = If (IsEven n) n ('S n)

-- singleton level
sNextEven :: SNat n -> SNat (NextEven n) 
sNextEven = undefined
