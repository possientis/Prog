import Control.Applicative
import Control.Monad
import Control.Monad.Trans

newtype ListT m a = ListT { run :: m [a] }

instance Monad m => Functor (ListT m) where
  fmap = liftM

instance Monad m => Applicative (ListT m) where
  pure  = return 
  (<*>) = ap

instance Monad m => Monad (ListT m) where
  return = ListT . return . return
  (>>=) k f = ListT $ do
    as <- run k
    liftM concat $ sequence (map (run . f) as)

instance Monad m => Alternative (ListT m) where
  empty = mzero
  (<|>) = mplus
  
instance Monad m => MonadPlus (ListT m) where
  mzero     = ListT $ return []
  mplus x y = ListT $ liftM2 mplus (run x) (run y)

     
instance MonadTrans ListT where
  lift = ListT . liftM return


bind :: (Monad m) => ListT m a -> (a -> ListT m b) -> ListT m b
bind k f = ListT $ run k  >>= \xs -> 
  mapM (run . f) xs       >>= \yss ->
  return $ concat yss
