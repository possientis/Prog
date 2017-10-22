module  MonadState
    (   State       (..)
    ,   get
    ,   put
    ,   modify
    ,   evalState
    ,   execState
    )   where

import Control.Monad (ap)

newtype State s a = State { runState :: s -> (a,s) }

instance Functor (State s) where
    fmap f u = pure f <*> u

instance Applicative (State s) where
    pure  = return
    (<*>) = ap 

instance Monad (State s) where
    return a = State $ \s -> (a,s)
    m >>= k  = State $ \s -> 
        let (a,t) = runState m s 
            in runState (k a) t
 
get :: State s s
get = State $ \s -> (s,s)

put :: s -> State s ()
put s = State $ \_ -> ((),s)

modify :: (s -> s) -> State s ()
modify f = get >>= \x -> put (f x)

evalState :: State s a -> s -> a
evalState m = fst . runState m

execState :: State s a -> s -> s
execState m = snd . runState m





