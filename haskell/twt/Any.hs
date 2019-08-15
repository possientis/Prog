{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ExistentialQuantification  #-}

-- GADTs syntax a lot clearer to define exitential types
data Any where
   Any :: a -> Any


-- somewhat confusing
data Any' = forall a . Any' a

to :: Any -> Any'
to (Any x) = Any' x

from :: Any' -> Any
from (Any' x) = Any x

-- not very useful
xs :: [Any]
xs =  [Any 'x', Any True, Any "hello"]

-- Given r, an instance of (forall a . a -> r) is constant
elimAny :: (forall a . a -> r) -> Any -> r
elimAny f (Any x) = f x

ex :: Any -> Int
ex = elimAny (const 5)








