{-# LANGUAGE RankNTypes             #-}

module  Optics.Adapter
    (   Adapter    (..)
    ,   AdapterP
    ,   toLense
    ,   toPrism
    ,   adapterC2P
    ,   adapterP2C
    ,   idC2C
    ,   idP2P
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

-- This proofs stands without assuming o i to be isomorphism.
idC2C :: Adapter s t a b -> Adapter s t a b
-- 1. idC2C x = adapterP2C  (adapterC2P x)
-- 2. idC2C (Adapter o i) = adapterP2C (adapterC2P (Adapter o i))
-- 3. idC2C (Adapter o i) = adapterP2C (dimap o i)
-- 4. idC2C (Adapter o i) = adapterI2C (adapterP2I (dimap o i))
-- 5. idC2C (Adapter o i) = adapterI2C (dimap o i (Iso id id))
-- 6. idC2C (Adapter o i) = adapterI2C (Iso (id . o) (i . id))
-- 7. idC2C (Adapter o i) = adapterI2C (Iso o i)
idC2C (Adapter o i) = Adapter o i

-- f :: p a b -> p s t , Iso id id :: Iso a b a b, p = Iso a b, 
idP2P :: AdapterP s t a b -> AdapterP s t a b
-- 1. idP2P f = adapterC2P (adapterP2C f)
-- 2. idP2P f = adapterC2P (adapterI2C (adapterP2I f))
-- 3, idP2P f = adapterC2P (adapterI2C (f (Iso id id)))
-- 4, idP2P f = let Iso o i = f (Iso id id) in adapterC2P (adapterI2C (Iso o i))
-- 5. idP2P f = let Iso o i = f (Iso id id) in adapterC2P (Adapter o i)
-- 6. idP2P f = let Iso o i = f (Iso id id) in dimap o i 
idP2P f pab = let Iso o i = f (Iso id id) in dimap o i pab -- = f pab ?


