{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}




import Data.Singletons.TH

$(promote [d|
    map :: (a -> b) -> [a] -> [b]
    map _ [] = []
    map f (x:xs) = f x : map f xs
    |])


infixr 5 :::

data HList (ts :: [*]) where
    Nil :: HList '[]
    (:::) :: t -> HList ts -> HList (t ': ts)


