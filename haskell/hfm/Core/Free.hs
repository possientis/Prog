{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeSynonymInstances  #-}

module Core.Free
  ( Free 
  , foldFree
  , liftF
  ) where

import Control.Monad (join, ap)

data FreeF f a r 
  = Pure a
  | Free (f r)

instance (Functor f) => Functor (FreeF f a) where
  fmap _ (Pure a)   = Pure a
  fmap f (Free fr)  = Free $ fmap f fr 

instance (Foldable f) => Foldable (FreeF f a) where
  foldMap _ (Pure _)   = mempty
  foldMap f (Free fr)  = foldMap f fr 

instance (Traversable f) => Traversable (FreeF f a) where
  traverse _ (Pure a)  = pure (Pure a)
  traverse f (Free fr) = Free <$> traverse f fr

newtype Free f a = Fix { unFix :: FreeF f a (Free f a) }

instance (Functor f) => Functor (Free f) where
  fmap = undefined

instance (Functor f) => Applicative (Free f) where
  pure  = return
  (<*>) = ap

instance (Functor f) => Monad (Free f) where
  return = Fix . Pure
  (>>=)  = bind

bind :: (Functor f) => Free f a -> (a -> Free f b) -> Free f b
bind k f = case unFix k of
  Pure a  -> f a
  Free (fa :: f (Free f a)) -> Fix (Free (fmap (flip bind f) fa))

foldFree :: (Monad m, Traversable f) => (f a -> m a) -> Free f a -> m a
foldFree eval act = case unFix act of
  Pure a  -> pure a
  Free fr -> join $ fmap eval $ traverse (foldFree eval) fr

liftF :: (Functor f) => f a -> Free f a
liftF fa = Fix (Free (fmap return fa))


