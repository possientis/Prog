{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module Recursive 
  (
  ) where

import Control.Monad (join)
import Data.Tuple.Extra

class (Functor b) => Recursive t b | t -> b where
  project :: t -> b t

class (Functor b) => Corecursive t b | t -> b where
  embed :: b t -> t

cata :: (Recursive t b) => (b a -> a) -> t -> a 
cata alg =  alg . fmap (cata alg) . project 

ana :: (Corecursive t b) => (a -> b a) -> a -> t
ana coalg = embed . fmap (ana coalg) . coalg 

cataM :: (Monad m, Traversable b, Recursive t b) => (b a -> m a) -> t -> m a
cataM algM = join . fmap algM . traverse (cataM algM) . project

anaM :: (Monad m, Traversable b, Corecursive t b) => (a -> m (b a)) -> a -> m t 
anaM coalgM = join . fmap (fmap embed . traverse (anaM coalgM)) . coalgM

para :: (Recursive t b) => (b (t,a) -> a) -> t -> a
para alg t =  alg . fmap ((t,) . para alg) . project $ t

apo  :: (Corecursive t b) => (a -> b (Either t a)) -> a -> t
apo coalg = embed . fmap (either id (apo coalg)) . coalg 

paraM :: (Monad m, Traversable b, Recursive t b) => (b (t,a) -> m a) -> t -> m a
paraM algM t = join . fmap algM . fmap (fmap (t,)) . traverse (paraM algM) . project $ t

apoM :: (Monad m, Traversable b, Corecursive t b) => (a -> m (b (Either t a))) -> a -> m t
apoM coalgM = fmap embed . join . fmap (traverse (either return (apoM coalgM))) . coalgM

