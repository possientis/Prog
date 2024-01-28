{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module Free
  (
  ) where

import Control.Monad (join, liftM2)
import Data.Functor.Identity

data FreeF f a r
  = Pure a
  | Free (f r)

caseFreeF :: (a -> b) -> (f r -> b) -> FreeF f a r -> b
caseFreeF p f = \case
  (Pure a)  -> p a
  (Free fr) -> f fr

instance Functor f => Functor (FreeF f a) where
  fmap f = caseFreeF Pure (Free . fmap f)

instance Foldable f => Foldable (FreeF f a) where
  foldMap f = caseFreeF (const mempty) (foldMap f)

instance Traversable f => Traversable (FreeF f a) where
  traverse f = caseFreeF (pure . Pure) (fmap Free . traverse f)

newtype FreeT f m a = FreeT {runFreeT :: m (FreeF f a (FreeT f m a))}

instance (Functor f, Functor m) => Functor (FreeT f m) where
  fmap f (FreeT ma) = FreeT . fmap (caseFreeF (Pure . f) (Free . fmap (fmap f))) $ ma

instance (Functor f, Monad m) => Applicative (FreeT f m) where
  pure = FreeT . pure . Pure
  (<*>) = liftM2 ($)

instance (Functor f, Monad m) => Monad (FreeT f m) where
  return = pure
  (>>=) (FreeT ma) f 
    = FreeT $ join . fmap (caseFreeF (runFreeT . f) (return . Free . fmap (>>= f))) $ ma

class Monad m => MonadFree f m | m -> f where
  wrap :: f (m a) -> m a

instance (Functor f, Monad m) => MonadFree f (FreeT f m) where
  wrap = FreeT . return . Free

class MonadTrans t where
  lift :: (Monad m) => m a -> t m a

instance MonadTrans (FreeT f) where
  lift = FreeT . fmap Pure

liftF :: (Functor f, MonadFree f m) => f a -> m a
liftF = wrap . fmap return 

wrapT :: (Functor f, MonadFree f m, MonadTrans t, Monad (t m)) => f (t m a) -> t m a
wrapT = join . lift . liftF

type Free f = FreeT f Identity

free :: FreeF f a (Free f a) -> Free f a
free = FreeT . return 

runFree :: Free f a -> FreeF f a (Free f a)
runFree (FreeT ma) = runIdentity ma

iterT :: (Functor f, Monad m) => (f (m a) -> m a) -> FreeT f m a -> m a
iterT alg (FreeT ma) = join . fmap (caseFreeF return (alg . fmap (iterT alg))) $ ma

iterTM 
  :: (Functor f, Monad m, MonadTrans t, Monad (t m))
  => (f (t m a) -> t m a)
  -> FreeT f m a 
  -> t m a
iterTM alg (FreeT ma) = do
  (a :: FreeF f a (FreeT f m a)) <- lift ma
  case a of 
    Pure a -> return a
    Free (fa :: f (FreeT f m a)) -> undefined 
        
