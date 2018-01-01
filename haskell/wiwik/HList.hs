{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}

infixr 5 :::

data HList (ts :: [*]) where
    Nil   :: HList '[]
    (:::) :: t -> HList ts -> HList (t ': ts) 


-- Take the head of a non-empty list with first value as Bool type
headBool :: HList (Bool ': xs) -> Bool
headBool (a ::: _) = a

hLength :: HList xs -> Int
hLength Nil         = 0
hLength (_ ::: xs)  = 1 + hLength xs


tuple :: (Bool, (String, (Double, ())))
tuple = (True, ("foo", (3.14, ())))


hList :: HList '[Bool, String, Double, ()]
hList = True ::: "foo" ::: 3.14 ::: () ::: Nil


main :: IO ()
main = do
    print $ headBool hList
    print $ hLength hList


