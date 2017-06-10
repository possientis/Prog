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

