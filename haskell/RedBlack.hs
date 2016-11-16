{-# LANGUAGE DataKinds, KindSignatures, GADTs #-}

type A = Int

data Color = R | B

data Nat = Zero | Suc Nat

data Tree :: Color -> Nat -> * where
  E   :: Tree B Zero
  TR  :: Tree B n -> A -> Tree B n -> Tree R n
  TB  :: Tree c1 n -> A -> Tree c2 n -> Tree B (Suc n) 


t1 = TR E 23 E
t2 = TB t1 12 E


data RBT :: * where
  Root :: Tree B n -> RBT

{-
bh :: RBT -> Nat
bh (Root t) = ... no runtime access to black height
-}

{- probably need a more recent verion of ghc 

type family Incr (c :: Color) (n :: Nat) :: Nat where
  Incr R n = n
  Incr B n = Suc n

-}
