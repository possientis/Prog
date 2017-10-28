{-# LANGUAGE GeneralizedNewtypeDeriving #-}

newtype Velocity =   Velocity 
    {   unVelocity :: Double 
    }   deriving (Eq,Ord)

newtype Quantity v a = Quantity a
        deriving (Eq, Ord, Num, Show)

data Haskeller
type Haskellers = Quantity Haskeller Int

a = Quantity 2 :: Haskellers
b = Quantity 6 :: Haskellers

totalHaskellers :: Haskellers
totalHaskellers = a + b
