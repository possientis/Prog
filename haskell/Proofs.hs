{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

data Z
data S n


data SNat n where
    Zero :: SNat Z
    Succ :: SNat n -> SNat (S n)

data Eql a b where
    Refl :: Eql a a

type family Add m n

type instance Add Z n = n
type instance Add (S m) n = S (Add m n)


add :: SNat m -> SNat n -> SNat (Add m n)
add Zero n = n
add (Succ m) n = Succ (add m n)

cong :: Eql a b -> Eql (f a) (f b)
cong Refl = Refl

plus_suc :: forall n. SNat n -> Eql (Add Z (S n)) (S n)
plus_suc Zero       = Refl
plus_suc (Succ n)   = cong (plus_suc n)


plus_zero :: forall n. SNat n -> Eql (Add Z n) n
plus_zero Zero = Refl
plus_zero (Succ n) = cong (plus_zero n)

-- need TypeOperators
data a :=: b where
    Refl' :: a :=: a

cong' :: a :=: b -> (f a) :=: (f b)
cong' Refl' = Refl'








