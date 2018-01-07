{-# LANGUAGE DeriveDataTypeable #-}

import Data.Typeable

data Animal = Cat | Dog deriving Typeable

data Zoo a = Zoo [a] deriving Typeable

-- returns true if of same types
equal :: (Typeable a, Typeable b) => a -> b -> Bool
equal a b = typeOf a == typeOf b


ex1 :: Bool
ex1 = equal Cat Dog

ex2 :: Bool
ex2 = equal (3::Int) Cat


ex3 :: TypeRep
ex3 = typeOf Cat                -- Animal

ex4 :: TypeRep
ex4 = typeOf (Zoo [Cat,Dog])    -- Zoo Animal

ex5 :: TypeRep
ex5 = typeOf ((1,3.14,"foo") :: (Int, Double, String))
-- (Int,Double,[Char])

ex6 :: Bool
ex6 = equal False ()            -- False

{-
Using the Typeable instance allows us to write down a type safe cast function
which can safely use unsafeCast and provide a proof that the resulting type
matches the input.
-}

{- unsafeCast does not work
cast :: (Typeable a, Typeable b) => a -> Maybe b
cast x
    | typeOf x == typeOf ret = Just ret
    | otherwise = Nothing
    where ret = unsafeCast x
-}



