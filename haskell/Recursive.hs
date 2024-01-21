{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module Recursive 
  (
  ) where

import Control.Monad (join, liftM2)
import Data.Tuple.Extra

data Cofree f a = Cofree a (f (Cofree f a))

data CofreeF f a r = CofreeF a (f r)

instance (Functor f) => Functor (CofreeF f a) where
  fmap f (CofreeF a fr) = CofreeF a (fmap f fr)

instance (Foldable f) => Foldable (CofreeF f a) where
  foldMap f (CofreeF _ fr) = foldMap f fr

instance (Traversable f) => Traversable (CofreeF f a) where
  traverse f (CofreeF a fr) = CofreeF a <$> traverse f fr

instance (Functor f) => Corecursive (Cofree f a) (CofreeF f a) where
  embed (CofreeF a fr) = Cofree a fr

unfold :: (Functor f) => (b -> (a, f b)) -> b -> Cofree f a
unfold = ana . (.) (uncurry CofreeF) 

unfoldM :: (Monad m, Traversable f, Functor f) => (b -> m (a, f b)) -> b -> m (Cofree f a)
unfoldM = anaM . (.) (fmap (uncurry CofreeF)) 

class (Functor b) => Recursive t b | t -> b where
  project :: t -> b t

class (Functor b) => Corecursive t b | t -> b where
  embed :: b t -> t

hylo :: (Functor f) => (f b -> b) -> (a -> f a) -> a -> b
hylo alg coalg = alg . fmap (hylo alg coalg) . coalg

hyloM :: (Monad m, Traversable f) => (f b -> m b) -> (a -> m (f a)) -> a -> m b
hyloM algM coalgM = join . fmap (join.fmap algM.traverse (hyloM algM coalgM)) . coalgM

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

histo :: (Recursive t b) => (b (Cofree b a) -> a) -> t -> a
histo alg = alg . fmap (unfold (histo alg &&& project)) . project

histoM :: (Monad m, Traversable b, Recursive t b) => (b (Cofree b a) -> m a) -> t -> m a
histoM algM = join . fmap algM . traverse f . project where
  f = unfoldM $ uncurry (liftM2 (,)) . (histoM algM &&& (return . project))
