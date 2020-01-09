{-# LANGUAGE RankNTypes             #-}

module  Optics.Adapter
    (   Adapter    (..)
    ,   AdapterP
    ,   toLense
    ,   toPrism
    ,   adapterC2P
    )   where

import Data.Profunctor

import Optics.Lens
import Optics.Prism
import Optics.Optic

data  Adapter s t a b 
    = Adapter 
    { from :: s -> a
    , to   :: b -> t 
    }

type AdapterP s t a b = forall p . Profunctor p => Optic p s t a b

-- Adapters are lenses
toLense :: Adapter s t a b -> Lens s t a b
toLense x = Lens view_ update_ where
    view_   = from x
    update_ = to x . fst
    
-- Adapters are prisms
toPrism :: Adapter s t a b -> Prism s t a b
toPrism x = Prism match_ build_ where
    match_ = Right . from x 
    build_ = to x 

adapterC2P :: Adapter s t a b -> AdapterP s t a b
adapterC2P (Adapter o i) = dimap o i

