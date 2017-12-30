{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}

data Nat = Z | S Nat

-- kind-indexed data family
data family Sing (a::k)

data instance Sing (a :: Nat) where
    SZ :: Sing 'Z
    SS :: Sing n -> Sing ('S n)

{-
 - Promoted Naturals
 - Value-level      Type-level          Models
 - SZ               Sing 'Z               0
 - SS SZ            Sing ('S 'Z)          1
 - SS (SS SZ)       Sing ('S ('S 'Z))     2
-}

x1 :: Sing 'Z
x1 =  SZ

x2 :: Sing ('S 'Z)
x2 =  SS SZ

x3 :: Sing ('S ('S 'Z))
x3 =  SS (SS SZ)

x4 :: Sing ('S ('S ('S 'Z)))
x4 =  SS (SS (SS SZ)) 


data instance Sing (a :: Maybe k) where
    SNothing :: Sing 'Nothing
    SJust    :: Sing x -> Sing ('Just x)


{-
 - Promoted Maybe
 - Value-level      Type-level          Models
 - SJust a          Sing ('Just a)      Just a 
 - SNothing         Sing Nothing        Nothing
-}

x5 :: Sing ('Just 'Z)
x5 =  SJust SZ

x6 :: Sing ('Just ('S 'Z))
x6 =  SJust x2

x7 :: Sing 'Nothing
x7 =  SNothing 


data instance Sing (a :: Bool) where
    STrue  :: Sing True
    SFalse :: Sing False

{-
 - Promoted Maybe
 - Value-level      Type-level          Models
 - STrue            Sing 'True          True
 - SFalse           Sing 'False         False
-}

x8 :: Sing 'True
x8 =  STrue

x9 :: Sing 'False
x9 =  SFalse

data Fin (n :: Nat) where
    FZ :: Fin (S n)
    FS :: Fin n -> Fin (S n)



data Vec a n where
    Nil  :: Vec a Z
    Cons :: a -> Vec a n -> Vec a (S n)


class SingI (a :: k) where
    sing :: Sing a

instance SingI Z where
    sing = SZ

instance SingI n => SingI (S n) where
    sing = SS sing

type SNat   (k :: Nat)              = Sing k
type SBool  (k :: Bool)             = Sing k
type SMaybe (b :: a) (k :: Maybe a) = Sing k

deriving instance Show Nat
deriving instance Show (SNat a)
deriving instance Show (SBool a)
deriving instance Show (Fin a)
deriving instance Show a => Show (Vec a n)

type family (m :: Nat) :+ (n :: Nat) :: Nat where
    Z   :+ n    = n
    S m :+ n    = S (m :+ n)

size :: Vec a n -> SNat n
size Nil            = SZ
size (Cons x xs)    = SS (size xs)

forget :: SNat n -> Nat
forget SZ       = Z
forget (SS n)   = S (forget n)

natToInt :: Integral n => Nat -> n
natToInt Z      = 0
natToInt (S n)  = natToInt n + 1

intToNat :: Integral n => n -> Nat
intToNat 0  = Z
intToNat n  = S $ intToNat (n - 1)     

sNatToInt :: Num n => SNat x -> n
sNatToInt SZ        = 0
sNatToInt (SS n)    = sNatToInt n + 1

index :: Fin n -> Vec a n -> a
index FZ (Cons x _)         = x
index (FS n) (Cons _ xs)    = index n xs

test1 :: Fin (S (S (S Z)))
test1 = FS (FS FZ)

test2 :: Int
test2 = index FZ (1 `Cons` (2 `Cons` Nil))

test3 :: Sing ('Just ('S ('S Z)))
test3 = SJust (SS (SS SZ))

test4 :: Sing ('S ('S Z))
test4 = SS (SS SZ)

-- polymorphic constructor SingI
test5 :: Sing ('S ('S Z))
test5 = sing



