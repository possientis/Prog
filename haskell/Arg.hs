{-# LANGUAGE FlexibleInstances #-}

class Arg a where
    collect' :: [String] -> a

-- IO () ... requires FlexibleInstances
instance Arg (IO ()) where
    collect' = mapM_ putStrLn

instance Arg [String] where
    collect' = id


instance (Show a, Arg r) => Arg (a -> r) where
    collect' acc =  \x -> collect' $ acc ++ [show x]


collect :: Arg t => t
collect = collect' []


example1 :: [String]
example1 = collect 'a' 2 3.0


example2 :: IO ()
example2 = collect () "foo" [1,2,3]

example3 :: [String]
example3 = collect

example4 :: [String]
example4 = collect 1


example5 :: [String]
example5 = collect 1 2
