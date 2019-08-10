{-# LANGUAGE RankNTypes     #-}
-- types 'a' and 'forall r . (a -> r) -> r' are isomorphic

-- appears to be a particular case of Yoneda when F = I
-- F : C -> Set 
-- F a ~ Nat[C(a,-), F]

to :: a -> (forall r . (a -> r) -> r)
to a f = f a

from :: (forall r . (a -> r) -> r) -> a
from f = f id
