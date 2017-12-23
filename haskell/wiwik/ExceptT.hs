{-# LANGUAGE    MultiParamTypeClasses, 
                FunctionalDependencies,
                FlexibleInstances          #-}


import Control.Monad
import Control.Monad.Trans
import Control.Exception.Base (IOException, ioError, catch)

newtype ExceptT e m a = ExceptT { runExceptT :: m (Either e a) }


instance (Monad m) => Functor (ExceptT e m) where
    fmap = (<*>) . pure 


instance (Monad m) => Applicative (ExceptT e m) where
    pure    = return
    (<*>)   = ap


instance (Monad m) => Monad (ExceptT e m) where
    return a = ExceptT $ return $ Right a
    m >>= k  = ExceptT $ do
        a <- runExceptT m
        case a of 
            Left e      -> return $ Left e
            Right a'    -> runExceptT $ k a'


throwE :: (Monad m) => e -> ExceptT e m a
throwE = ExceptT . return . Left

-- e' potentially different error type, in case of exception in handler
catchE :: (Monad m) => ExceptT e m a            -- ^ the inner computation
                    -> (e -> ExceptT e' m a)    -- ^ handler for exceptions
                    -> ExceptT e' m a
catchE m k = ExceptT $ do
    a <- runExceptT m
    case a of
        Left e  -> runExceptT (k e)
        Right r -> return (Right r)


instance MonadTrans (ExceptT e) where 
    lift x = ExceptT $ liftM Right x 

-- need language extensions
class (Monad m) => MonadError e m | m -> e where
    throwError :: e -> m a
    catchError :: m a -> (e -> m a) -> m a


instance (Monad m) => MonadError e (ExceptT e m) where
    throwError = throwE
    catchError = catchE

instance MonadError IOException IO where
    throwError = ioError
    catchError = catch 

instance MonadError e (Either e) where
    throwError = Left
    catchError (Left e) k   = k e
    catchError (Right x) _  = Right x




