module Identity
  ( Id(..)
  ) where
 
import Control.Applicative
import Control.Monad
import Control.Monad.Trans

newtype Id a = Id { runIdentity :: a }

instance Functor Id where
  fmap = liftM

instance Applicative Id where
  pure  = return
  (<*>) = ap

instance Monad Id where
  return = Id
  (>>=) k f = f $ runIdentity k


newtype IdentityT m a = IdentityT { run :: m (Id a) }

instance Monad m => Functor (IdentityT m) where
  fmap = liftM

instance Monad m => Applicative (IdentityT m) where
  pure = return
  (<*>) = ap

instance Monad m => Monad (IdentityT m) where
  return    = IdentityT . return . return 
  (>>=) k f = IdentityT $ do
    Id a <- run k
    run $ f a

instance MonadTrans IdentityT where
  lift = IdentityT . liftM Id




