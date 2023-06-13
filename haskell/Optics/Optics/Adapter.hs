{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FunctionalDependencies     #-}

module  Optics.Adapter
    (   AdapterC    (..)
    ,   AdapterP    
    ,   Adapter     (..)
    ,   Iso         (..)
    ,   toLense
    ,   toPrism
    ,   adapterC2P
    ,   adapterP2C
    ,   idC2C
    ,   idP2P
    ,   fromP
    ,   toP
    )   where

import Data.Profunctor

import Optics.Lens
import Optics.Prism
import Optics.Optic

data  AdapterC a b s t 
    = AdapterC 
    { fromC :: s -> a
    , toC   :: b -> t 
    }

type AdapterP a b s t = forall p . Profunctor p => Optic p a b s t

-- Adapters are lenses
toLense :: AdapterC a b s t -> LensC a b s t
toLense x = LensC view_ update_ where
    view_   = fromC x
    update_ = toC x . fst
    
-- Adapters are prisms
toPrism :: AdapterC a b s t -> PrismC a b s t 
toPrism x = PrismC match_ build_ where
    match_ = Right . fromC x 
    build_ = toC x 

adapterC2P :: AdapterC a b s t -> AdapterP a b s t
adapterC2P (AdapterC o i) = dimap o i

instance Profunctor (AdapterC a b) where
    dimap l r (AdapterC o i) = AdapterC (o . l) (r . i) 


adapterP2C :: AdapterP a b s t -> AdapterC a b s t
adapterP2C f = f (AdapterC id id) 

-- This proofs stands without assuming o i to be isomorphism.
idC2C :: AdapterC a b s t -> AdapterC a b s t 
-- 1. idC2C x = adapterP2C  (adapterC2P x)
-- 2. idC2C (AdapterC o i) = adapterP2C (adapterC2P (AdapterC o i))
-- 3. idC2C (AdapterC o i) = adapterP2C (dimap o i)
-- 4. idC2C (AdapterC o i) = dimap o i (AdapterC id id)
-- 5. idC2C (AdapterC o i) = AdapterC (id . o) (i . id)
-- 6. idC2C (AdapterC o i) = AdapterC o i
idC2C = id

-- f :: p a b -> p s t , AdapterC id id :: AdapterC a b a b, p = AdapterC a b, 
idP2P :: AdapterP a b s t -> AdapterP a b s t 
-- 1. idP2P f k = adapterC2P (adapterP2C f) k
-- 2. idP2P f k = adapterC2P (f (AdapterC id id)) k
-- 3. idP2P f k = flip adapterC2P k (f (AdapterC id id))
-- 4. idP2P f k = f (flip adapterC2P k (AdapterC id id)) -- see paper
-- 5. idP2P f k = f (adapterC2P (AdapterC id id) k)
-- 6. idP2P f k = f (dimap id id k)
-- 7. idP2P f k = f k
-- 8.idP2P f = f
idP2P x = id x -- point free appears to fail

-- point-free definition will fail
fromP :: AdapterP a b s t -> s -> a
fromP f = fromC (adapterP2C f)

-- point-free definition will fail
toP :: AdapterP a b s t -> b -> t
toP f = toC (adapterP2C f)

class Adapter a b s t optics | optics -> a b s t where
    from   :: optics -> s -> a
    to :: optics -> b -> t

instance Adapter a b s t (AdapterC a b s t) where
    from = fromC
    to   = toC

-- illegal 
-- instance Adapter a b s t (AdapterP a b s t) where

newtype Iso a b s t = Iso { unIso :: AdapterP a b s t }
   
instance Adapter a b s t (Iso a b s t) where
    from (Iso f) = fromP f
    to   (Iso f) = toP f

