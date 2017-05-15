import Control.Applicative
import Control.Monad
import Control.Monad.Trans

newtype MaybeT m a = MaybeT { run :: m (Maybe a) } 

instance Monad m => Applicative (MaybeT m) where
  pure  = return
  (<*>) = ap

instance Monad m => Functor (MaybeT m) where
  fmap = liftM

instance Monad m => Alternative (MaybeT m) where
  empty = mzero
  (<|>) = mplus

instance Monad m => Monad (MaybeT m) where
  return = MaybeT . return . Just   -- MaybeT . return . return is less readable
  (>>=) k f = MaybeT $ do
    a <- run k
    case a of 
      Nothing   -> return Nothing
      Just a'   -> run $ f a'

instance Monad m => MonadPlus (MaybeT m) where
  mzero     = MaybeT $ return Nothing
  mplus x y = MaybeT $ liftM2 mplus (run x) (run y)

-- class MonadTrans (t :: (* -> *) -> * -> *) where
--  lift :: Monad m => m a -> t m a

instance MonadTrans MaybeT where
  lift = MaybeT . liftM Just

isValid :: String -> Bool
isValid s = length s >= 8 

getValidPassword :: MaybeT IO String
getValidPassword = do
  s <- lift getLine
  guard (isValid s)
  return s

askPassword :: MaybeT IO ()
askPassword = do
  lift $ putStrLn "Insert your new password:"
  value <- getValidPassword
  lift $ putStrLn $ "Storing in database..." ++ (show value)


main :: IO ()
main = do 
  c <- run askPassword
  case c of 
    Just () -> putStrLn "Just () was returned"
    Nothing -> putStrLn "Nothing was returned" 











