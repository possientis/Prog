module PMD  -- Poor man's debugging
  ( Pmd(..)
  ) where

import Control.Applicative
import Control.Monad



newtype Pmd a = Pmd { run :: (a, IO ()) }

instance Applicative Pmd where
  pure  = return 
  (<*>) = ap 

instance Functor Pmd where 
  fmap = liftM

instance Monad Pmd where
  (>>=) (Pmd (x, prt)) f = let (Pmd (v, prt')) = f x in Pmd (v, prt >>prt')
  return x = Pmd (x, return ())


instance (Show a) => Show (Pmd a) where
  show (Pmd (x, _)) = show x


