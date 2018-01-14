{-# LANGUAGE DeriveDataTypeable #-}

import Data.Data
import Data.Typeable
import Control.Monad.Identity

data Animal = Cat | Dog deriving (Data, Typeable)


newtype Val = Val Int deriving (Show, Data, Typeable)

incr :: Typeable a => a -> a
incr = maybe id id (cast f) where 
    f :: Val -> Val
    f (Val x) = Val (x*100)

over :: Data a => a -> a
over x = runIdentity $ gfoldl cont base (incr x) where
    cont k d = k <*> (pure $ over d)
    base = pure


ex1 :: Constr
ex1 = toConstr Dog  
-- Dog

ex2 :: DataType
ex2 = dataTypeOf Cat
-- DataType {tycon = "Animal", datarep = AlgRep [Cat,Dog]}


ex3 :: [Val]
ex3 = over [Val 1, Val 2, Val 3]
-- [Val 100,Val 200,Val 300]

ex4 :: (Val,Val,Val)
ex4 = over (Val 1, Val 2, Val 3)
-- (Val 100,Val 200,Val 300)

numHoles :: Data a => a -> Int
numHoles = gmapQl (+) 0 (const 1)

ex5 :: Int
ex5 = numHoles (1::Int,2::Int,3::Int,4::Int,5::Int,6::Int,7::Int)
-- 7

ex6 :: Int
ex6 = numHoles (Just 'a')
-- 1



