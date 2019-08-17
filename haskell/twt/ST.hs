import Data.IORef
import System.IO.Unsafe

newtype ST s a = ST { unsafeRunST :: a }

instance Functor (ST s) where
    fmap f (ST a) = seq a $ ST (f a)

instance Applicative (ST s) where
    pure  = ST
    (ST f) <*> (ST a) = seq f $ seq a $ ST (f a)

instance Monad (ST s) where
    return       = pure
    (ST a) >>= f = seq a $ f a  

newtype STRef s a = STRef { unSTRef :: IORef a }

newSTRef_ :: a -> STRef s a
newSTRef_ = STRef . unsafePerformIO . newIORef

newSTRef :: a -> ST s (STRef s a)
newSTRef = pure . newSTRef_

readSTRef_ :: STRef s a -> a
readSTRef_ = unsafePerformIO . readIORef . unSTRef

readSTRef :: STRef s a -> ST s a
readSTRef = pure . readSTRef_

writeSTRef_ :: STRef s a -> a -> ()
writeSTRef_ ref = unsafePerformIO . writeIORef (unSTRef ref)

writeSTRef :: STRef s a -> a -> ST s ()
writeSTRef ref = pure . writeSTRef_ ref

modifySTRef :: STRef s a -> (a -> a) -> ST s ()
modifySTRef ref f = do
    a <- readSTRef ref
    writeSTRef ref $ f a
