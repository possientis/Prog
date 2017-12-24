{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}


import GHC.TypeLits
import Data.Type.Equality

data Vec :: Nat -> * -> * where
    Nil  :: Vec 0 a
    Cons :: a -> Vec n a -> Vec (1 + n) a 

instance Show (Vec 0 a) where
    show Nil = "Nil"

vec3 :: Vec 3 Int
vec3 = 0 `Cons` (1 `Cons` (2 `Cons` Nil))


data Foo :: Nat -> * where
    Small    :: (n <= 2) => Foo n
    Big      :: (3 <= n) => Foo n
    Empty    :: ((n == 0) ~ True) => Foo n
    NonEmpty :: ((n == 0) ~ False) => Foo n


big :: Foo 10
big = Big

small :: Foo 2
small = Small

empty :: Foo 0
empty = Empty

nonempty :: Foo 3
nonempty = NonEmpty


