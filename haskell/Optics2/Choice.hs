module Choice
  ( Choice
  , left
  , right
  ) where

import Profunctor


-- Def: a Profunctor p is said to be Choice, if and only, there exists a map 
-- 'left` which extends every transformation of type a ~> b to a transformation 
-- of type Either a c ~> Either b c

class (Profunctor p) => Choice p where
  left :: p a b -> p (Either a c) (Either b c)

-- Remark: If p is a Choice Profunctor, then any transformation of type a ~> b can
-- also be extended to an transformation of type Either c a ~> Either c b. This motivates
-- the following definition:

right :: (Choice p) => p a b -> p (Either c a) (Either c b)
right = dimap swap swap . left where 
  swap = either Right Left
      

-- Lemma: the Profunctor (->) is Choice.
instance Choice (->) where
  left f = either (Left . f) Right
