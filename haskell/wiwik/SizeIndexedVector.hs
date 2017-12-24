{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

data Nat = Z | S Nat deriving (Eq, Show)

-- Z and S are data constructor, not type constructor.
-- They can be promoted to the type level with DataKinds

type Zero   = Z
type One    = S Zero
type Two    = S One
type Three  = S Two
type Four   = S Three
type Five   = S Four 


data Vec :: Nat -> * -> * where
    Nil     :: Vec Z a
    Cons    :: a -> Vec n a -> Vec (S n) a

instance (Show a) => Show (Vec n a) where
    show Nil            = "Nil"
    show (Cons x xs)    = "Cons " ++ show x ++ " (" ++ show xs ++ ")" 

class FromList n where 
    fromList :: [a] -> Vec n a


instance FromList Z where
    fromList []     = Nil
    fromList (x:xs) = error "fromList : expecting [] argument"

instance (FromList n) => FromList (S n) where
    fromList []     = error "fromList : expecting non-empty list"
    fromList (x:xs) = Cons x $ fromList xs

ex1 :: Vec Zero Int
ex1 = fromList []

ex2 :: Vec Zero Int
ex2 = fromList [7]   -- runtime error

ex3 :: Vec One Int
ex3 = fromList [7]

ex4 :: Vec Two Int
ex4 = fromList [7,13]

ex5 :: Vec Two Int
ex5 = fromList [6,12]

lengthVec :: Vec n a -> Nat
lengthVec Nil           = Z
lengthVec (Cons x xs)   = S (lengthVec xs)


zipVec :: Vec n a -> Vec n b -> Vec n (a,b)
zipVec Nil Nil                  = Nil
zipVec (Cons x xs) (Cons y ys)  = Cons (x,y) $ zipVec xs ys

ex6 :: Vec Two (Int,Int)
ex6 = zipVec ex4 ex5

-- ex7 = zipVec ex3 ex4 -- compile-time error

vec4 :: Vec Four Int
vec4 = fromList [0,1,2,3]


vec5 :: Vec Five Int
vec5 = fromList [0,1,2,3,4]

ex7 :: Nat
ex7 = lengthVec vec4

ex8 :: Vec Four (Int,Int)
ex8 = zipVec vec4 vec4
