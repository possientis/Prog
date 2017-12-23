{-# LANGUAGE GADTs #-}

data Free f a where
    Pure :: a -> Free f a
    Free :: f (Free f a) -> Free f a


data Cofree f a where
    Cofree :: a -> f (Cofree f a) -> Cofree f a

testCofree :: Cofree Maybe Int
testCofree = (Cofree 1 (Just (Cofree 2 Nothing)))
    


