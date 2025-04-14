{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

import Prelude hiding (Bool, True, False)

data Unit where
    TT :: Unit

data Bool where
    True  :: Bool
    False :: Bool

data Nat where
    Zero :: Nat
    Succ :: Nat -> Nat

isZero :: Nat -> Bool
isZero Zero = True
isZero _    = False

pred :: Nat -> Nat
pred Zero = Zero
pred (Succ n) = n
    
plus :: Nat -> Nat -> Nat
plus Zero m     = m
plus (Succ p) m = Succ (plus p m)

data List a where
    Nil  :: List a 
    Cons :: a -> List a -> List a



