module  Optics.Profunctor
    (   UpStar  (..)
    )   where

import Data.Profunctor

data UpStar f a b = Upstar { unUpStar :: a -> f b }


instance (Functor f) => Profunctor (UpStar f) where
    dimap k l h = undefined 
