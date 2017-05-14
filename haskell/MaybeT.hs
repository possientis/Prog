import Control.Applicative
import Control.Monad

newtype MaybeT m a = MaybeT { run :: m (Maybe a) } 

instance Monad m => Applicative (MaybeT m) where
  pure  = return
  (<*>) = ap

instance Monad m => Functor (MaybeT m) where
  fmap = liftM

instance Monad m => Monad (MaybeT m) where
  return = MaybeT . return . Just   -- MaybeT . return . return is less readable
  (>>=) k f = MaybeT $ do
    a <- run k
    case a of 
      Nothing   -> return Nothing
      Just a'   -> run $ f a'
