{-# LANGUAGE FlexibleInstances #-}  -- GHC type system, more powerful than Haskell 98

data Foo a = Foo a

instance Functor Foo where
  fmap f (Foo a) = Foo (f a)

-- -XFlexibleInstances required to allow use of GHC type system
-- which is more powerful than the Haskell 98 standard
instance Functor (Either Int) where
  fmap _ (Left n)   = Left n
  fmap f (Right r)  = Right (f r)
