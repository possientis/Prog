module Cont
  ( Cont
  , cont
  , runCont
  ) where

import Control.Applicative
import Control.Monad
 
newtype Cont r a = Cont { runCont :: (a -> r) -> r }

cont :: ((a -> r) -> r) -> Cont r a 
cont = Cont

instance Functor (Cont r) where
  fmap = liftM

instance Applicative (Cont r) where 
  pure  = return 
  (<*>) = ap

instance Monad (Cont r) where
  return x  = cont ($ x)
  m >>= f   = cont $ \k -> runCont m $ \x -> runCont (f x) $ k

add :: Int -> Int -> Cont r Int
add x y = return $ x + y

mult :: Int -> Int -> Cont r Int
mult x y = return $ x * y

ex1 :: IO ()
ex1 = print $ runCont (f >>= g) id where
    f = add 1 2
    g = mult 3

class (Monad m) => MonadCont m where
    callCC :: ((a -> m b) -> m a) -> m a

instance MonadCont (Cont r) where
    callCC = undefined
