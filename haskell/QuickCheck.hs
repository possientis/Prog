import Test.QuickCheck



myList :: Arbitrary a => Gen [a]
myList = oneof
    [ return []
    , (:) <$> arbitrary <*> myList
    ]

myList' :: Arbitrary a => Gen [a]
myList' = frequency 
    [ (1, return [])
    , (4, (:) <$> arbitrary <*> myList')
    ]

-- sized :: (Int -> Gen a) -> Gen a

flexList :: Arbitrary a => Gen [a]
flexList = sized $ \n ->
    frequency
        [ (1, return [])
        , (n, (:) <$> arbitrary <*> flexList)
        ]

main :: IO ()
main = do
    sample $ (flexList :: Gen [Int])




