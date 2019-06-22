module DualVariableSub
  ( dual
  ) where

import Data.Set
import Formula


dual :: (Eq v, Ord v) => (v -> w) -> (v -> w) -> Formula v -> Set v -> Formula w
dual f0 f1 = f where
  f (Belong x y)  u  = belong (g x u) (g y u) 
  f (Bot)         u  = bot
  f (Imply p q)   u  = imply (f p u) (f q u)
  f (Forall x p)  u  = forall (f1 x) $ f p (delete x u)
  g z u = if z `elem` u then f0 z else f1 z


