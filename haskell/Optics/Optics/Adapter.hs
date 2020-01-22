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

data  Adapter a b s t 
    = Adapter 
    { from :: s -> a
    , to   :: b -> t 
    }

type AdapterP a b s t = forall p . Profunctor p => Optic p a b s t

-- Adapters are lenses
toLense :: Adapter a b s t -> Lens a b s t
toLense x = Lens view_ update_ where
    view_   = from x
    update_ = to x . fst
    
-- Adapters are prisms
toPrism :: Adapter a b s t -> Prism a b s t 
toPrism x = Prism match_ build_ where
    match_ = Right . from x 
    build_ = to x 

adapterC2P :: Adapter a b s t -> AdapterP a b s t
adapterC2P (Adapter o i) = dimap o i

instance Profunctor (Adapter a b) where
    dimap l r (Adapter o i) = Adapter (o . l) (r . i) 

--TODO
adapterP2C :: AdapterP a b s t -> Adapter a b s t
adapterP2C _f = undefined

-- This proofs stands without assuming o i to be isomorphism.
idC2C :: Adapter a b s t -> Adapter a b s t 
-- 1. idC2C x = adapterP2C  (adapterC2P x)
-- 2. idC2C (Adapter o i) = adapterP2C (adapterC2P (Adapter o i))
-- 3. idC2C (Adapter o i) = adapterP2C (dimap o i)
-- 4. idC2C (Adapter o i) = adapterI2C (adapterP2I (dimap o i))
-- 5. idC2C (Adapter o i) = adapterI2C (dimap o i (Iso id id))
-- 6. idC2C (Adapter o i) = adapterI2C (Iso (id . o) (i . id))
-- 7. idC2C (Adapter o i) = adapterI2C (Iso o i)
-- 8. idC2C (Adapter o i) = Adapter o i
idC2C = id

-- f :: p a b -> p s t , Iso id id :: Iso a b a b, p = Iso a b, 
idP2P :: AdapterP a b s t -> AdapterP a b s t 
-- 1. idP2P f k = adapterC2P (adapterP2C f) k
-- 2. idP2P f k = adapterC2P (adapterI2C (adapterP2I f)) k
-- 3. idP2P f k = adapterC2P (adapterI2C (f (Iso id id))) k
-- 4. idP2P f k = flip adapterC2P k (adapterI2C (f (Iso id id)))
-- 5. idP2P f k = f (flip adapterC2P k (adapterI2C (Iso id id)))  -- see paper
-- 6. idP2P f k = f (adapterC2P (adapterI2C (Iso id id)) k)
-- 7. idP2P f k = f (adapterC2P (Adapter id id) k)
-- 8. idP2P f k = f (dimap id id k)
-- 9. idP2P f k = f k
-- 10.idP2P f = f
idP2P = id
