import Test.QuickCheck
import Test.QuickCheck.Instances ()
import Data.ByteString.Base64 
import Data.ByteString as B


main :: IO ()
main = do
    quickCheck prop_sizeRatio

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

prop_sizeRatio :: ByteString -> Bool
prop_sizeRatio bs = B.length (encode bs) 
    == 4 * ceiling (fromIntegral (B.length bs) / 3 :: Double)


