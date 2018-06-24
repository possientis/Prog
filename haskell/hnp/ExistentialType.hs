{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}

data S = forall a. Show a => S a

data S' where
    S' :: Show a => a -> S'

instance Show S where
    show (S a) = show a


ss :: [S]
ss = [S 5, S "test", S 3.0]


main :: IO ()
main = do
    mapM_ print ss
    print $ genShow show ss


genShow :: (forall a. Show a => a -> String) -> [S] -> [String]
genShow f = map (\(S a) -> f a)
