{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE TypeOperators      #-}


module  Optics.Profunctor
    (   UpStar      (..)
    ,   Cartesian   (..)
    ,   Cocartesian (..)
    ,   Monoidal    (..)
    ,   cross
    ,   plus
    ,   fork
    )   where

import Data.Profunctor

type a :*: b = (a,b)
type a :+: b = Either a b


data UpStar f a b = UpStar { unUpStar :: a -> f b }


instance (Functor f) => Profunctor (UpStar f) where
    dimap k l (UpStar h) = UpStar $ fmap l . h . k


class Profunctor p => Cartesian p where
    first  :: p a b -> p (a,c) (b,c)
    second :: p a b -> p (c,a) (c,b)

class Profunctor p => Cocartesian p where
    left  :: p a b -> p (Either a c) (Either b c)
    right :: p a b -> p (Either c a) (Either c b)

class Profunctor p => Monoidal p where
    par :: p a1 b1 -> p a2 b2 -> p (a1 :*: a2) (b1 :*: b2)
    empty :: p () ()

cross :: (a1 -> b1) -> (a2 -> b2) -> a1 :*: a2 -> b1 :*: b2
cross f1 f2 (x1,x2) = (f1 x1, f2 x2)

fork :: (a -> b) -> (a -> c) -> a -> b :*: c
fork f g x = (f x, g x)

plus :: (a1 -> b1) -> (a2 -> b2) -> a1 :+: a2 -> b1 :+: b2
plus f1 _ (Left x1)  = Left  (f1 x1)
plus _ f2 (Right x2) = Right (f2 x2)

instance Cartesian (->) where
    first  f = cross f id
    second f = cross id f

instance Cocartesian (->) where
    left f  = plus f id
    right f = plus id f

instance Monoidal (->) where
    par = cross
    empty = id

rstrength :: Functor f => (f a, b) -> f (a,b)
rstrength (fa,b) = fmap (,b) fa

lstrength :: Functor f => (a, f b) -> f (a,b)
lstrength (a, fb) = fmap (a,) fb

pair :: Applicative f 
     => (a1 -> f b1) 
     -> (a2 -> f b2) 
     -> (a1 :*: a2) 
     -> f (b1 :*: b2)
pair h1 h2 (x1,x2) = pure (,) <*> h1 x1 <*> h2 x2

instance Functor f => Cartesian (UpStar f) where
    first  (UpStar h) = UpStar $ rstrength . cross h id
    second (UpStar h) = UpStar $ lstrength . cross id h

instance Applicative f => Cocartesian (UpStar f) where
    left  (UpStar h) = UpStar $ either (fmap Left . h) (pure . Right)
    right (UpStar h) = UpStar $ either (pure . Left) (fmap Right . h)

instance Applicative f => Monoidal (UpStar f) where
    par (UpStar h1) (UpStar h2) = UpStar $ pair h1 h2
    empty = UpStar pure


