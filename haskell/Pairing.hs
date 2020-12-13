{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

--type Pairing f g = forall a b. f (a -> b) -> g a -> b


import Data.Functor.Identity


class Pairing f g | f -> g, g -> f where
    pair :: (a -> b -> c) -> f a -> g b -> c

instance Pairing Identity Identity where
    pair f (Identity a) (Identity b) = f a b


instance Pairing ((->) a) ((,) a) where
    pair f g (a,b) = f (g a) b 

uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry = pair ($)



