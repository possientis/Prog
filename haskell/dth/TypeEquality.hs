{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

--import Data.Type.Equality

data (a::k) :~: (b::k) where
  Refl :: a :~: a

castWith :: (a :~: b) -> a -> b
castWith Refl x = x 

-- equivalent way
data (a::k) :=: (b::k) = (a ~ b) => Refl'


