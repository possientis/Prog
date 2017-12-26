{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE KindSignatures #-}
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
    FZ :: Fin Z
    FS :: Fin n -> Fin (S n)

x10 :: Fin Z
x10 = FZ

x11 :: Fin (S Z)
x11 = FS x10

data Vec a n where
    Nil  :: Vec a Z
    Cons :: a -> Vec a n -> Vec a (S n)


class SingI (a :: k) where
    sing :: Sing a

instance SingI Z where
    sing = SZ

instance SingI n => SingI (S n) where
    sing = SS sing

type SNat  (k :: Nat)  = Sing k
type SBool (k :: Bool) = Sing k

deriving instance Show Nat
deriving instance Show (SNat a)
deriving instance Show (SBool a)
deriving instance Show (Fin a)
deriving instance Show a => Show (Vec a n)

-- TODO







