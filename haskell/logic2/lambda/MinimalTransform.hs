module MinimalTransform
  ( minTrans
  ) where

import Data.Functor

import Bar
import Formula
import Substitution
import Valid

import Test_data

minTrans :: (Eq v, Ord v) => Formula v -> Formula (Bar v)
minTrans (Variable x) = Variable (left x)
minTrans (Apply p q)  = Apply (minTrans p) (minTrans q)
minTrans (Lambda x p) = Lambda (right n) $ ((right n)<-:(left x)) <$> q 
  where
  q = minTrans p
  n = nValid q x

-- nValid p x = n where n is smallest integer such that (n<-:x) valid for p
nValid :: (Eq v, Ord v) => Formula (Bar v) -> v -> Int
nValid p x = go p x 0 where
  go p x n = if isValidFor ((right n) <-: (left x)) p 
              then n
              else go p x (n+1) 
