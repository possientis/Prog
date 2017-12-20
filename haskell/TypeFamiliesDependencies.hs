{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE PolyKinds #-}

type family F a b c = (result :: k) | result -> a b c

type instance F Int Char Bool = Bool
type instance F Char Bool Int = Int
type instance F Bool Int Char = Char
