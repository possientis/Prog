import qualified Prelude
import Prelude hiding (Num)

class Num a where
    (+) :: a -> a -> a
    (*) :: a -> a -> a
    negate :: a -> a


data DNum a = DNum 
    { dAdd :: a -> a -> a
    , dMul :: a -> a -> a
    , dNeg :: a -> a
    }

add (DNum a m n) = a
mul (DNum a m n) = m
neg (DNum a m n) = n

numDInt :: DNum Int
numDInt = DNum plusInt mulInt negInt

plusInt :: Int -> Int -> Int 
plusInt n m = n Prelude.+ m


mulInt :: Int -> Int -> Int 
mulInt n m = n Prelude.* m


negInt :: Int -> Int
negInt n = Prelude.negate n

