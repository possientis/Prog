module Strong
  ( Strong
  , first
  , second
  ) where

import Data.Tuple (swap)
import Data.Tuple.Extra ((***))
import Profunctor


-- Def: a Profunctor p is said to be Strong, if and only, there exists a map 
-- 'first` which extends every transformation of type a ~> b to a transformation 
-- of type (a,c) ~> (b,c)

class (Profunctor p) => Strong p where
  first :: p a b -> p (a,c) (b,c)

-- Remark: If p is a Strong Profunctor, then any transformation of type a ~> b can
-- also be extended to an transformation of type (c,a) ~> (c,b). This motivates
-- the following definition:

second :: (Strong p) => p a b -> p (c,a) (c,b)
second = dimap swap swap . first

-- Lemma: the Profunctor (->) is Strong.
instance Strong (->) where
  first f = f *** id 
