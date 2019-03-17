import Prelude hiding (Eq (..))
import qualified Prelude as P

class Eq a where
    (==) :: a -> a -> Bool
    (/=) :: a -> a -> Bool
    (/=) x y = not (x == y)


data Eq' a = MkEq
    { eq :: a -> a -> Bool
    , ne :: a -> a -> Bool
    }

eqInt :: Int -> Int -> Bool
eqInt = (P.==)


instance Eq Int where
    (==) = eqInt

dEqInt :: Eq' Int
dEqInt  = MkEq
    { eq = eqInt
    , ne = \x y -> not (eqInt x y)
    }

instance (Eq a) => Eq [a] where
    []     == []     = True
    (x:xs) == (y:ys) = x == y && xs == ys
    _      == _      = False
    
dEqList :: Eq' a  -> Eq' [a]
dEqList d = MkEq el nl where
    el [] []         = True
    el (x:xs) (y:ys) = eq d x y && el xs ys
    el _ _           = False
    nl xs ys         = not $ el xs ys

member :: (Eq a) => a -> [a] -> Bool
member _ []     = False
member x (y:ys)
    | x == y    = True
    | otherwise = member x ys


member' :: Eq' a -> a -> [a] -> Bool
member' _ _ []  = False
member' d x (y:ys)
    | eq d x y  = True
    | otherwise = member' d x ys




