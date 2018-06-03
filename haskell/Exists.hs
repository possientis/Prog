{-# Language ExistentialQuantification #-}

data T = forall a . Show a => MkT a

instance Show T where
    show (MkT x) = show x


t1 :: T
t1 = MkT (3 :: Int)


t2 :: T
t2 = MkT True

t3 :: T
t3 = MkT "foo"


l :: [T]
l = [t1, t2,t3]


main :: IO ()
main = do
    print l
    putStrLn $ show' showInt 3


data ShowImpl a = MkShowImpl (a -> String)

show' :: ShowImpl a -> a -> String
show' (MkShowImpl f) x = f x

showInt :: ShowImpl Int
showInt = MkShowImpl show





