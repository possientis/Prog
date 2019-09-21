module Formula
    (   Formula (..)
    ,   (<<=)
    ,   valid
    )   where

import Lam.T  
import Fol.P

import qualified Lam.Free       as T
import qualified Lam.Dmap       as T
import qualified Lam.Order      as T
import qualified Lam.Bound      as T
import qualified Lam.Variable   as T
import qualified Lam.Subformula as T

import qualified Fol.Free       as P
import qualified Fol.Dmap       as P
import qualified Fol.Order      as P
import qualified Fol.Bound      as P
import qualified Fol.Variable   as P
import qualified Fol.Subformula as P

class (Functor f) => Formula f where
    var   ::            f v -> [v]
    free  :: (Eq v) =>  f v -> [v] 
    bnd   ::            f v -> [v]
    sub   ::            f v -> [f v]
    ord   ::            f v -> Integer
    dmap  :: (Eq v) => (v -> w) -> (v -> w) -> f v -> f w


instance Formula T where
    var     = T.var
    free    = T.free
    bnd     = T.bnd
    sub     = T.sub
    ord     = T.ord
    dmap    = T.dmap

instance Formula P where
    var     = P.var
    free    = P.free
    bnd     = P.bnd
    sub     = P.sub
    ord     = P.ord
    dmap    = P.dmap

-- 'is a subformula of' relation
(<<=) :: (Formula f, Eq (f v)) => f v -> f v -> Bool
(<<=) s t = s `elem` sub t

-- 'is valid substitution for' relation
valid :: (Formula f, Eq v, Eq w) => (v -> w) -> f v -> Bool
valid f t = all cond xs where
    cond (s,x) = (f x) `elem` free (fmap f s) 
    xs = [(s,x)| s <- sub t, x <- free s]


