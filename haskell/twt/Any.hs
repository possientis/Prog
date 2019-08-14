{-# LANGUAGE GADTs                      #-}
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



