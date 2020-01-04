{-# LANGUAGE TupleSections      #-}


module  Optics.Profunctor
    (   UpStar      (..)
    ,   Cartesian   (..)
    )   where

import Data.Profunctor

data UpStar f a b = Upstar { unUpStar :: a -> f b }


instance (Functor f) => Profunctor (UpStar f) where
    dimap k l (Upstar h) = Upstar $ fmap l . h . k


class Profunctor p => Cartesian p where
    first  :: p a b -> p (a,c) (b,c)
    second :: p a b -> p (c,a) (c,b)


cross :: (a1 -> b1) -> (a2 -> b2) -> (a1,a2) -> (b1,b2)
cross f g (x,y) = (f x, g y)

instance Cartesian (->) where
    first  f = cross f id
    second f = cross id f

instance Functor f => Cartesian (UpStar f) where
    first  (Upstar h) = Upstar $ \(a,c) -> fmap (,c) (h a) 
    second (Upstar h) = Upstar $ \(c,a) -> fmap (c,) (h a)

rstrength :: Functor f => (f a, b) -> f (a,b)
rstrength (fa,b) = fmap (,b) fa




