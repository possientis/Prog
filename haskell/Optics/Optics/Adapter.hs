{-# LANGUAGE RankNTypes             #-}

module  Optics.Adapter
    (   Adapter    (..)
    ,   AdapterP
    ,   toLense
    ,   toPrism
    ,   adapterC2P
    ,   adapterP2C
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

data  Iso a b s t 
    = Iso
    { _from :: s -> a
    , _to   :: b -> t
    }

instance Profunctor (Iso a b) where
    dimap l r (Iso o i) = Iso (o . l) (r . i) 

adapterI2C :: Iso a b s t -> Adapter s t a b
adapterI2C (Iso o i) = Adapter o i

adapterP2I :: AdapterP s t a b -> Iso a b s t
adapterP2I f = f (Iso id id) 

adapterP2C :: AdapterP s t a b -> Adapter s t a b
adapterP2C f = adapterI2C (adapterP2I f)

idC2C :: Adapter s t a b -> Adapter s t a b
idC2C x = adapterP2C  (adapterC2P x)
