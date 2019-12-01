{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ScopedTypeVariables    #-}

import Data.Kind

data Nat = Z | S Nat

data FunList a b t = Done t | More a (FunList a b (b -> t))

out :: FunList a b t -> Either t (a, FunList a b (b -> t))
out (Done t)    = Left t
out (More x l)  = Right (x,l) 

inn :: Either t (a, FunList a b (b -> t)) -> FunList a b t
inn (Left t)        = Done t
inn (Right (x,l))   = More x l


-- (inn . out) (Done t)   = inn (Left t) = Done t
-- (inn . out) (More x l) = inn (Right (x,l)) = More x l

-- (out . inn) (Left t) = out (Done t) = Left t
-- (out . inn) (Right (x,l)) = out (More x l) = Right (x,l)

data Fin (n :: Nat) :: Type where
    FZ :: Fin ('S n)
    FS :: Fin n -> Fin ('S n)

-- a^n x (b^n -> t), need to separate case n = 0 
type FunList_ (n :: Nat) a b t = (Fin n -> a, (Fin n -> b) -> t)

-- (b , Fin n -> b) and Fin (S n) -> b are isomorphic
to1 :: (b, Fin n -> b) -> Fin ('S n) -> b
to1 (b, _) FZ      = b
to1 (_, bn) (FS n) = bn n

class From1 (n :: Nat) where
    from1 :: (Fin ('S n) -> b) -> (b, Fin n -> b)
    
instance From1 'Z where
    from1 bn' = (bn' FZ, absurd)



{-
-- (Fin (S n) -> b) -> t  and (Fin n -> b) -> b -> t are isomorphic
to1 :: ((Fin n -> b) -> b -> t) -> (Fin ('S n) -> b) -> t
to1 bn b bn' 
-}

{-
-- (a, FunList_ n a b (b -> t)) isomorphic to FunList_ (n + 1) a b t
to :: forall n a b t . (a, FunList_ n a b (b -> t)) -> FunList_ ('S n) a b t
to (xa, (fa,fb)) = (ga,gb) where
    ga :: Fin ('S n) -> a
    ga FZ     = xa
    ga (FS n) = fa n
    gb :: (Fin ('S n) -> b) -> t
    gb = x 
-}

data FunList' a b t where
    FunList' :: FunList_ n a b t -> FunList' a b t

absurd :: Fin 'Z -> a
absurd x = case x of {}



{-
-- FunList a b t and FunList' a b t are isomorphic
-- can we 'prove' this ?

from :: FunList a b t -> FunList' a b t 
from (Done t)   = FunList' (Left t)
from (More a l) = FunList' (Right (f1,f2)) where
    f1 FZ     = a
    f1 (FS n) = undefined k
    f2 = undefined 
-}


