{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module StateT 
  ( StateT 
  , state
  )
  where

import Control.Monad

-- Attempting to guess what an implementation of StateT is

newtype StateT s m a = StateT { runStateT :: s -> m (a, s) }

-- hiding implementation detail
state :: Monad m => (s -> m (a, s)) -> StateT s m a
state = StateT

-- 'get' is meant to return the state of a state monad. In this case,
-- part of the 'state' is hidden in the monad 'm'. Hence, we can only
-- hope to retrieve a partial state, so to speak.

get :: Monad m =>  StateT s m s  
get = state $ \s -> return (s, s)

-- 'put' is meant to set the state of a state monad.
put :: Monad m => s -> StateT s m ()
put s = state $ \_ -> return ((), s) 

-- 'modify' changes state based on current state and transition function

modify :: Monad m => (s -> s) -> StateT s m ()
modify f = get >>= put . f  -- computation of new state lazy, how would you do strict?

modify' :: Monad m => (s -> s) -> StateT s m ()
modify' f = do
  s <- get
  put (f s)

modify'' :: Monad m => (s -> s) -> StateT s m ()
modify'' f = state $ \s -> return ((), f s)


-- 'gets' allows to retrieve properties of the state, based on a projection function

gets :: Monad m => (s -> a) -> StateT s m a
gets f = get >>= return . f


gets' :: Monad m => (s -> a) -> StateT s m a
gets' f = do
  s <- get
  return (f s)

gets'' :: Monad m => (s -> a) -> StateT s m a
gets'' f = state $ \s -> return (f s, s)



-- first things first, we need to have a monad
instance Monad m => Monad (StateT s m) where
  return a  = state $ \s -> return (a, s) 
  m >>= f   = state $ \s -> runStateT m s >>= \(a,t) -> runStateT (f a) t


-- 'evalStateT' aims at returning the value. Ideally we would like to have 
-- evalStateT :: StateT s m a -> s -> a, but this cannot be. why?
-- Let m :: StateT s m a. let t :: s. We are not going to achieve 
-- anything unless we unpack m with runStateT, giving us a :: s -> m (a, s)
-- We can apply this function to our argument t , obtaining some m (a, s)
-- However, we cannot hope to get the result of this computation unless
-- we 'run' it. Hence we need to step inside the monad 'm' and we cannot
-- hope to return an 'a' when coming out. The best we can hope for is an 'm a'

evalStateT :: Monad m => StateT s m a -> s -> m a
evalStateT m s = runStateT m s >>= return . fst

evalStateT' :: Monad m => StateT s m a -> s -> m a
evalStateT' m s = do  -- inside the 'm' monad
  (a, t) <- runStateT m s
  return a 


execStateT :: Monad m => StateT s m a -> s -> m s
execStateT m s = runStateT m s >>= return . snd

execStateT' :: Monad m => StateT s m a -> s -> m s
execStateT' m s = do  -- inside the 'm' monad
  (a, t) <- runStateT m s
  return t

mapStateT :: Monad m => ((a, s) -> (b, s)) -> StateT s m a -> StateT s m b 
mapStateT f k = state $ \s -> runStateT k s >>= return . f

mapStateT' :: Monad m => ((a, s) -> (b, s)) -> StateT s m a -> StateT s m b 
mapStateT' f k = do
  a <- k
  s <- get
  let (b, t) = f (a, s)
  put t
  return b


lift1 :: Monad m => m a -> StateT s m a
lift1 m = state $ \s -> m >>= \a -> return (a, s)

lift2 :: Monad m => (s -> (a, s)) -> StateT s m a
lift2 f = state $ \s -> return (f s)













