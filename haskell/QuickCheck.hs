{-# LANGUAGE OverloadedStrings  #-}

import Data.Char
import Data.Monoid
import Test.QuickCheck
import Text.Regex.Posix
import Data.ByteString as B
import Data.ByteString.Base64 
import Test.QuickCheck.Instances ()

main :: IO ()
main = do
    quickCheck prop_sizeRatio
    quickCheck prop_endsWithPadding

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

prop_endsWithPadding :: ByteString -> Property
prop_endsWithPadding  b 
    = collect suffix 
    $ (encoding =~ ("(^|[^=])" <> suffix <> "$"))   -- at end
    && not (encoding =~ ("=[^=]" :: ByteString))    -- only at end

    where
    encoding = encode b
    suffix   = B.replicate num (fromIntegral $ ord '=')
    num      = case B.length b `mod` 3 of
        0   -> 0
        1   -> 2
        2   -> 1
        _   -> error "cannot happen" 


