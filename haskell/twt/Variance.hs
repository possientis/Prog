{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

import Data.Functor.Contravariant

-- Functor
newtype T1 a = T1 (Int -> a)            -- :: * -> *
    deriving Functor

-- Contravariant
newtype T2 a = T2 (a -> Int)            -- :: * -> *
--    deriving Contravariant            -- fails even with GenDeriving

-- Nothing
newtype T3 a = T3 (a -> a)              -- :: * -> * 

-- Contravariant
newtype T4 a = T4 ((Int -> a) -> Int)   -- :: * -> *

-- Functor
newtype T5 a = T5 ((a -> Int) -> Int)   -- :: * -> *
    deriving Functor                    -- clever enough

instance Contravariant T2 where
    contramap f (T2 g) = T2 (g . f)     -- not much implementation choice


instance Contravariant T4 where
    contramap f (T4 g) = T4 (\h -> g (f . h)) -- not much choice
