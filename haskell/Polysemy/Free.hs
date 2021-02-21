module  Free
    (   Free        (..) 
    ,   TeletypeF   (..)    -- TODO: clean up
    ,   toFree
    ,   fromFree
    )   where

import Control.Monad

import Teletype

data Free f k
    = Pure k
    | Impure (f (Free f k)) 

instance Functor f => Functor (Free f) where
    fmap g (Pure a)    = Pure   $ g a
    fmap g (Impure fa) = Impure $ fmap (fmap g) fa

instance Functor f => Applicative (Free f) where
    pure  = return 
    (<*>) = ap

instance Functor f => Monad (Free f) where
    return = Pure
    (>>=) (Pure k) g = g k
    (>>=) (Impure k) g = Impure undefined

-- k :: f (Free f a)
-- (>>=) :: Free f a -> (a -> Free f b) -> Free f b
-- g :: a -> Free f b
-- _ :: f (Free f b)

data TeletypeF r 
    = WriteLineF String r
    | ReadLineF (String -> r)

instance Functor TeletypeF where
    fmap f (WriteLineF s a) = WriteLineF s (f a)
    fmap f (ReadLineF g)    = ReadLineF (f . g)

toFree :: Teletype a -> Free TeletypeF a
toFree (Done a)        = Pure a
toFree (WriteLine s k) = Impure (WriteLineF s (toFree k))
toFree (ReadLine g)    = Impure (ReadLineF (toFree . g))

fromFree :: Free TeletypeF a -> Teletype a
fromFree (Pure a)                  = Done a
fromFree (Impure (WriteLineF s k)) = WriteLine s (fromFree k)
fromFree (Impure (ReadLineF g))    = ReadLine (fromFree . g)

