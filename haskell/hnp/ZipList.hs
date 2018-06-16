{-# LANGUAGE GeneralizedNewtypeDeriving #-}

newtype ZipList a = ZipList { getZipList :: [a] } deriving Functor


instance Applicative ZipList where
    pure x = ZipList (repeat x)
    ZipList fs <*> ZipList xs = ZipList (zipWith ($) fs xs)


transpose :: [[a]] -> [[a]]
transpose = getZipList . sequenceB . fmap ZipList

sequenceB :: (Applicative f) => [f a] -> f [a]
sequenceB []        = pure []
sequenceB (x:xs)    = (:) <$> x <*> sequenceB xs


ex = [[1,2,3,30],[4,5,6,60],[7,8,9,90]]

main :: IO ()
main = do
    print $ transpose ex


