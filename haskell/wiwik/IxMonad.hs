{-# LANGUAGE RebindableSyntax #-}

import Prelude hiding (fmap, (>>=), (>>), return)
import Data.IORef

class IxMonad md where
    return :: a -> md i i a
    (>>=)  :: md i m a -> (a -> md m o b) -> md i o b



newtype IState i o a = IState { runIState :: i -> (a,o) }


evalIState :: IState i o a -> i -> a
evalIState m i = fst $ runIState m i

execIState :: IState i o a -> i -> o
execIState m i = snd $ runIState m i


ifThenElse :: Bool -> a -> a -> a
ifThenElse b i j = case b of
    True    -> i
    False   -> j

instance IxMonad IState where
    return a = IState $ \i -> (a,i) 
    v >>= f  = IState $ \i -> 
        let (a,m) = runIState v i in
            runIState (f a) m

fmap :: (a -> b) -> IState i o a -> IState i o b
fmap f v = IState $ \i -> let (a,o) = runIState v i in (f a, o)


join :: IState i m (IState m o a) -> IState i o a
join v = IState $ \i -> let (w,m) = runIState v i in
    runIState w m

(>>) :: IState i m a -> IState m o b -> IState i o b
v >> w = v >>= \_ -> w


get :: IState s s s
get = IState $ \s -> (s,s)

gets :: (a -> o) -> IState a o a
gets f = IState $ \s -> (s, f s)

put :: o -> IState i o ()
put o = IState $ \_ -> ((),o)

modify :: (i -> o) -> IState i o ()
modify f = IState $ \i -> ((), f i)


data Locked = Locked
data Unlocked = Unlocked

type Stateful a = IState a Unlocked a

acquire :: IState i Locked ()
acquire = put Locked

-- can only release the lock if it's held, try release
-- the lock that is not held is now a type error.
release :: IState Locked Unlocked ()
release = put Unlocked


-- Statically forbids improper handling of resources.
lockExample :: Stateful a
lockExample = do    -- RebindableSyntax
    ptr <- get :: IState a a a
    acquire    :: IState a Locked ()
-- ...
    release    :: IState Locked Unlocked ()
    return ptr

{-
failure1 :: Stateful a
failure1 = do
    ptr <- get
    acquire
    return ptr  -- didn't release
-}

{-
failure2 :: Stateful a
failure2 = do
    ptr <- get
    release     -- didn't acquire
    return ptr
-}

evalReleased :: IState i Unlocked a -> i -> a
evalReleased f i = evalIState f i

example :: IO (IORef Integer)
example = evalReleased <$> pure lockExample <*> newIORef 0









