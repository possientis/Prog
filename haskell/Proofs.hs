{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

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

-- TODO






