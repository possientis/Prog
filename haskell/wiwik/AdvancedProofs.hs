{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE KindSignatures #-}

import Prelude hiding (reverse)
import Data.Type.Equality

data Nat = Z | S Nat

data IsNat n where
     ZeroIsNat :: IsNat Z
     SuccIsNat :: IsNat n -> IsNat (S n)

data Vec  :: * -> Nat -> * where
     Nil  :: Vec a Z
     Cons :: a -> Vec a n -> Vec a (S n)


instance Show a => Show (Vec a n) where
    show Nil         = "Nil"
    show (Cons x xs) = "Cons " ++ show x ++ " (" ++ show xs ++ ")" 


type family (n :: Nat) :+ (m :: Nat) :: Nat where
    Z   :+ n    = n
    S n :+ m    = S (n :+ m) 

-- a ~ b implies  f a ~ f b 
cong :: a :~: b -> f a :~: f b
cong Refl = Refl


-- a ~ b implies (f a) implies (f b)
rewrite :: a :~: b -> f a -> f b
rewrite Refl x = x

-- will fail to type check unless PolyKinds
plus_zero :: forall n. IsNat n -> (n :+ Z) :~: n
plus_zero ZeroIsNat = Refl
plus_zero (SuccIsNat p) = cong (plus_zero p)

plus_n_Sm :: forall n m. IsNat n -> IsNat m -> (n :+ (S m)) :~: S (n :+ m)
plus_n_Sm ZeroIsNat _     = Refl
plus_n_Sm (SuccIsNat p) q = cong (plus_n_Sm p q)


proofOfSize :: Vec a n -> IsNat n
proofOfSize Nil          = ZeroIsNat
proofOfSize (Cons x xs)  = SuccIsNat (proofOfSize xs)

reverse :: forall n a. Vec a n -> Vec a n
reverse xs = rewrite (plus_zero (proofOfSize xs)) $  go Nil xs
    where
    go :: Vec a m -> Vec a k -> Vec a (k :+ m)
    go acc Nil          = acc
    go acc (Cons x xs)  = rewrite 
        (plus_n_Sm (proofOfSize xs) (proofOfSize acc)) $ 
            go (Cons x acc) xs

append :: Vec a n -> Vec a m -> Vec a (n :+ m)
append (Cons x xs)  ys = Cons x (append xs ys)
append Nil          ys = ys 

vec :: Vec Int (S (S (S Z)))
vec = 1 `Cons` (2 `Cons` (3 `Cons` Nil))


test :: Vec Int (S (S (S Z)))
test = reverse vec




