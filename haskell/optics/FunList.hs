{-# LANGUAGE GADTs              #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE KindSignatures     #-}

import Data.Kind
import GHC.TypeLits

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
    FZ :: Fin (n + 1)
    FS :: Fin n -> Fin (n + 1)

-- a^n x (b^n -> t), need to separate case n = 0 
type FunList_ (n :: Nat) a b t = Either t (Fin n -> a, (Fin n -> b) -> t)


data FunList' a b t where
    FunList' :: FunList_ n a b t -> FunList' a b t

-- FunList a b t and FunList' a b t are isomorphic
-- can we 'prove' this ?

from :: FunList a b t -> FunList' a b t 
from (Done t)   = FunList' (Left t)
from (More a l) = FunList' (Right (f1,f2)) where
    f1 FZ     = a
    f1 (FS n) = undefined 
    f2 = undefined 



