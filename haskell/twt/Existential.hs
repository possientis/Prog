{-# LANGUAGE GADTs          #-}
{-# LANGUAGE RankNTypes     #-}

data HasShow where
    HasShow :: (Show a) => a -> HasShow

{-
instance Show HasShow where
    show (HasShow s) = "HasShow " ++ show s
-}

example :: [HasShow]
example =  [HasShow 'a', HasShow "hello", HasShow True]

elimHasShow
    :: (forall a . Show a => a -> r)
    -> HasShow
    -> r
elimHasShow f (HasShow a) = f a

-- cool 
instance Show HasShow where
    show = elimHasShow show


