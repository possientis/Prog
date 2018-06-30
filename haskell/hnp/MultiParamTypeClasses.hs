{-# LANGUAGE MultiParamTypeClasses #-}

class Convertible a b where
    convert :: a -> b

instance Convertible Int Float where
    convert = fromIntegral
