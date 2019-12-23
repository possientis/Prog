{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE UndecidableInstances   #-}

module  Optics.IsEven
    (   IsEven
    ,   isEven
    ,   sIsEven
    ,   nextEven
    ,   NextEven
    ,   sNextEven
    )   where



import Optics.If
import Optics.Nat
import Optics.Singleton


-- term level
isEven :: Nat -> Bool 
isEven Z = True
isEven (S Z) = False
isEven (S (S n)) = isEven n

-- type level
type family IsEven (n :: Nat) :: Bool where
    IsEven  'Z = 'True
    IsEven ('S 'Z) = 'False 
    IsEven ('S ('S n)) = IsEven n

-- singleton level
sIsEven :: SNat n -> SBool (IsEven n)
sIsEven SZ = STrue
sIsEven (SS SZ) = SFalse
sIsEven (SS (SS n)) = sIsEven n

-- term level
nextEven :: Nat -> Nat 
nextEven n = if isEven n then n else S n 

-- type level
type family NextEven (n :: Nat) :: Nat where
    NextEven n = If (IsEven n) n ('S n)

-- singleton level
sNextEven :: SNat n -> SNat (NextEven n) 
sNextEven n = sIf (sIsEven n) n (SS n)


