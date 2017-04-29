{-# LANGUAGE FlexibleInstances #-}

import Data.Monoid
import Control.Monad

instance MonadPlus m => Monoid (m a) where
  mempty  = mzero
  mappend = mplus




