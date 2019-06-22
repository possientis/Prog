module AlphaEquiv
  ( alphaEq
  ) where

import Data.Functor ((<$>))
import Data.Set
import Formula
import Variable
import Substitution
import Data.List

alphaEq :: (Eq v, Ord v) => Formula v -> Formula v -> Bool
alphaEq (Belong x y) (Belong x' y') = (x == x') && (y == y')
alphaEq (Bot) (Bot)                 = True
alphaEq (Imply p q) (Imply p' q')   = alphaEq p p' && alphaEq q q'
alphaEq (Forall x p) (Forall x' p') = if (x == x') 
  then  alphaEq p p'
  else (not $ member x' $ free p) && alphaEq ((x<->x')<$>p) p'
alphaEq _ _                         = False


{-
alphaEq :: (Eq v, Ord v) => Formula v -> Formula v -> Bool
alphaEq p q = equal' ([],p) ([],q)

equal' :: (Eq v, Ord v) =>  ([v], Formula v) -> ([v], Formula v) -> Bool
equal' (xs, Belong x1 x2) (ys, Belong y1 y2) 
    =   equalVar (xs,x1) (ys,y1) 
    &&  equalVar (xs,x2) (ys,y2)
equal' (xs, Bot) (ys, Bot) = True
equal' (xs, Imply p q) (ys, Imply p' q')     
    =   equal' (xs,p) (ys, p') 
    &&  equal' (xs,q) (ys,q')
equal' (xs, Forall x p) (ys, Forall y p') 
    = equal' (x:xs,p) (y:ys,p')
equal' _ _ = False
 
equalVar :: (Eq v, Ord v) => ([v],v) -> ([v],v) -> Bool
equalVar (xs,x) (ys,y) = case (elemIndex x xs, elemIndex y ys) of
    (Just i, Just j)    -> (i == j)
    (Nothing, Nothing)  -> (x == y)
    _                   -> False

-}


{-
equalVar :: (Eq v, Ord v) => [(v,v)] -> v -> v -> Bool
equalVar [] x y             = (x == y)
equalVar ((x,y):bound) z w  = (x == z && y == w) 
                           || (x /= z && y /= w && equalVar bound z w) 

equal' :: (Eq v, Ord v) => [(v,v)] -> Formula v -> Formula v -> Bool
equal' bound (Belong x1 y1) (Belong x2 y2)  = (equalVar bound x1 x2 && equalVar bound y1 y2)
equal' bound (Bot) (Bot)                    = True
equal' bound (Imply u1 v1) (Imply u2 v2)    = equal' bound u1 u2 && equal' bound v1 v2
equal' bound (Forall x u) (Forall y v)      = equal' ((x,y):bound) u v
equal' _ _ _                                = False

equal :: (Eq v, Ord v) => Formula v -> Formula v -> Bool
equal e1 e2 = equal' [] e1 e2
-}



