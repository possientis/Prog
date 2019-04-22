{-# LANGUAGE OverloadedStrings  #-}

import Data.Char
import Data.Word
import Data.Monoid
import Data.Either
import Test.QuickCheck
import Text.Regex.Posix
import Data.ByteString.Base64 
import Test.QuickCheck.Instances ()
import qualified Data.Set as S
import qualified Data.ByteString as B

type ByteString = B.ByteString

main :: IO ()
main = do
    quickCheck prop_sizeRatio
    quickCheck prop_endsWithPadding
    quickCheck prop_outputAlphabet
    quickCheck prop_outputAlphabet'     -- fails, insufficient coverage
    quickCheck prop_outputAlphabet''
    quickCheck prop_dec_enc
    quickCheck prop_enc_dec
    quickCheck prop_enc_dec'

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


-- Just add this to the beginning of the property
-- collect :: (Show a, Testable prop) => a -> prop -> Property

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


-- classify :: Testable prop 
--          => Bool
--          -> String
--          -> prop 
--          -> Property

prop_outputAlphabet :: ByteString -> Property
prop_outputAlphabet bs 
    = classify (S.size used >= 32) "half-alphabet" 
    $ classify (S.size used >= 63) "full-alphabet"
    $ used `S.isSubsetOf` allowed where
        used    = S.fromList . B.unpack $ encode bs
        allowed = S.fromList . map (fromIntegral . ord)  $ 
            ['A'..'Z'] <> ['a'..'z'] <> ['0'..'9'] <> ['+','/','=']

-- insisting on coverage of 1% full-alphabet
prop_outputAlphabet' :: ByteString -> Property
prop_outputAlphabet' bs 
    = cover (S.size used >= 63) 1 "full-alphapbet" 
    $ used `S.isSubsetOf` allowed where
        used    = S.fromList . B.unpack $ encode bs
        allowed = S.fromList . map (fromIntegral . ord)  $ 
            ['A'..'Z'] <> ['a'..'z'] <> ['0'..'9'] <> ['+','/','=']



-- To use a custom generator in a Property use
-- forAll :: (Show a, Testable prop)
--        => Gen a -> (a -> prop) -> Property

prop_outputAlphabet'' :: Property
prop_outputAlphabet'' = 
    forAll (scale (*3) (arbitrary :: Gen ByteString)) $ \bs -> let 
        used    = S.fromList . B.unpack $ encode bs
        allowed = S.fromList . map (fromIntegral . ord)  $ 
            ['A'..'Z'] <> ['a'..'z'] <> ['0'..'9'] <> ['+','/','=']
        in 
        cover (S.size used >= 63) 1 "full-alphapbet" 
        $ used `S.isSubsetOf` allowed

prop_dec_enc :: ByteString -> Bool
prop_dec_enc bs = decode (encode bs) == Right bs

-- very inefficient coz unlikely to generate a valid Base64 string
-- (==>) :: Testable prop => Bool -> prop -> Property
prop_enc_dec :: ByteString -> Property
prop_enc_dec bs = legit ==> [bs] == rights [encode <$> dec] where
    dec   = decode bs
    legit = isRight dec

-- better use a custom generator with forAll
encoded :: Gen ByteString
encoded = do
    body <- concat <$> listOf (group 0) 
    end  <- group =<< choose (0, 2)
    return . B.pack $ body <> end
    where
    group :: Int -> Gen [Word8]
    group pad = do
        letters <- vectorOf (4 - pad)
                .  elements . map (fromIntegral . ord) 
                $ ['A'..'Z'] <> ['a'..'z'] <> ['0'..'9'] <> ['+','/']
        return $ letters <> replicate pad 61 -- 61 is ascii for '='

-- test still fails with this generator due to non-canonical encodings
-- see https://tools.ietf.org/html/rfc4648.html#section-3.5
prop_enc_dec' :: Property
prop_enc_dec' = forAll encoded $ \bs -> 
    [bs] == rights [encode <$> decode bs]  


