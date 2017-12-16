{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

import Data.Char

class Convertible a b 
--    | a -> b  -- create functional dependencies conflict (Integer or Char)
    where
    convert :: a -> b

instance Convertible Int Integer where
    convert = toInteger

instance Convertible Int Char where
    convert = chr

instance Convertible Char Int where
    convert = ord

