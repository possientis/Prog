{-# LANGUAGE TypeOperators #-}

module  Assumption
    (   Assump  (..)
    ,   find
    )   where

import Subst
import Syntax
import Scheme

data Assump = Id :>: Scheme


instance Types Assump where
    apply s (i :>: sc)  = i :>: (apply s sc)
    tv (_ :>: sc)       = tv sc


find :: Monad m => Id -> [Assump] -> m Scheme
find i []                   = fail $ "unbound identifier: " ++ i
find i ((j :>: sc) : as)    = if i == j then return sc else find i as


