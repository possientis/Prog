module MinimalTransform
  (
  ) where

import Bar
import Formula
import Substitution

minTrans :: (Eq v) => Formula v -> Formula (Bar v)
minTrans (Belong x y) = Belong (Left x) (Left y)
minTrans (Bot)        = Bot
minTrans (Imply p q)  = Imply (minTrans p) (minTrans q)
minTrans (Forall x p) = Forall (Right n) $ ((Right n)<-:(Left x)) <$> q 
  where
  q = minTrans p
  n = 0

