import Control.Applicative
import Control.Monad
import Control.Monad.Trans

newtype Identity a = Identity { runIdentity :: a }

instance Functor Identity where
  fmap = liftM

instance Applicative Identity where
  pure  = return
  (<*>) = ap

instance Monad Identity where
  return = Identity
  (>>=) k f = f $ runIdentity k


newtype IdentityT m a = IdentityT { run :: m (Identity a) }

instance Monad m => Functor (IdentityT m) where
  fmap = liftM

instance Monad m => Applicative (IdentityT m) where
  pure = return
  (<*>) = ap

instance Monad m => Monad (IdentityT m) where
  return    = IdentityT . return . return 
  (>>=) k f = IdentityT $ do
    Identity a <- run k
    run $ f a

instance MonadTrans IdentityT where
  lift = IdentityT . liftM Identity

IdentityT SomeMonad a -- SomeMonad a

SomeMonadT Identity a -- Identity (SomeMonad a)



