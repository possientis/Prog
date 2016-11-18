import Number

--import Control.Monad.CryptoRandom
import System.Entropy (getEntropy)
import Crypto.Random
--import Crypto.Classes hiding (hash)
--import Crypto.Classes.Exceptions hiding (hash)
--import Crypto.HMAC hiding (hash)
--import Crypto.Modes hiding (hash)
--import Crypto.Padding hiding (hash)
--import Crypto.Random hiding (hash)
--import Crypto.Types hiding (hash)
--import Crypto.Util hiding (hash)

-- import Data.Tagged
import Data.Binary


import qualified Data.ByteString.Lazy as BS
import Data.Word
import Data.Bits 

type ByteString = BS.ByteString

x = zero :: Number
y = one :: Number
z = fromInteger 23 :: Number
t = fromInteger $ -3 :: Number
a = fromInteger 0xfffefdfcfbfaf9f8f7 :: Number



testWord8 :: IO ()
testWord8 = do
  putStrLn "Testing type Word8 ..."
  putStrLn $ "minBound = " ++ show (minBound :: Word8)
  putStrLn $ "maxBound = " ++ show (maxBound :: Word8)
  let x = toEnum 255 :: Word8
  putStrLn $ "x = toEnum 255 = " ++ show x
  putStrLn $ "bit 0 = " ++ show (bit 0 :: Word8)
  putStrLn $ "bit 1 = " ++ show (bit 1 :: Word8)
  putStrLn $ "bit 2 = " ++ show (bit 2 :: Word8)
  putStrLn $ "bit 3 = " ++ show (bit 3 :: Word8)
  putStrLn $ "bit 4 = " ++ show (bit 4 :: Word8)
  putStrLn $ "bit 5 = " ++ show (bit 5 :: Word8)
  putStrLn $ "bit 6 = " ++ show (bit 6 :: Word8)
  putStrLn $ "bit 7 = " ++ show (bit 7 :: Word8)
  putStrLn $ "bit 7 of 128 = " ++ show (testBit (0x80::Word8) 7)
  

testByteString :: IO ()
testByteString = do
  putStrLn $ "empty = " ++ show BS.empty
  putStrLn $ "singleton 255 = " ++ (show $ BS.singleton 255)
  putStrLn $ "pack [0,1,34,208, 255] = " ++ (show $ BS.pack [0, 1, 34, 208, 255])
  putStrLn $ "unpack (singleton 255) = " ++ (show $ BS.unpack (BS.singleton 255))

  

testNumber :: IO ()
testNumber = do
  putStrLn "Testing Number API ..."
  putStrLn $ "x = " ++ (show x)
  putStrLn $ "y = " ++ (show y)
  putStrLn $ "z = " ++ (show z)
  putStrLn $ "t = " ++ (show t)
  putStrLn $ " x == y : " ++ (show (x == y))
  putStrLn $ " x <= y : " ++ (show (x <= y))
  putStrLn $ "-x = " ++ (show $ negate x)
  putStrLn $ "-y = " ++ (show $ negate y)
  putStrLn $ "fromInteger 45 = " ++ (show $ fromInteger 45)
  putStrLn $ "z + t = " ++ (show $ z + t)
  putStrLn $ "z * t = " ++ (show $ z * t)
  putStrLn $ "signum z = " ++ (show $ signum z)
  putStrLn $ "sign z = " ++ (show $ sign z)
  putStrLn $ "signum t = " ++ (show $ signum t)
  putStrLn $ "sign t = " ++ (show $ sign t)
  putStrLn $ "signum x = " ++ (show $ signum x)
  putStrLn $ "sign x = " ++ (show $ sign x)
  putStrLn $ "toInteger z = " ++ (show $ toInteger z)
  putStrLn $ "hash x = " ++ (show $ hash x)
  putStrLn $ "hash y = " ++ (show $ hash y)
  putStrLn $ "hash z = " ++ (show $ hash z)
  putStrLn $ "hash t = " ++ (show $ hash t)
  putStrLn $ "a = " ++ (show a)
  let (Just bytes) = toBytes a (NumBytes 32) 
  putStrLn $ "toBytes a 32 = " ++ (show bytes)
  let (Just b) = fromBytes (Sign 1) bytes     :: Maybe Number
  let (Just c) = fromBytes (Sign $ -1) bytes  :: Maybe Number
  putStrLn $ "b = " ++ (show b)
  putStrLn $ "c = " ++ (show c)
  putStrLn $ "bitLength 0 = " ++ (show $ bitLength (fromInteger 0 :: Number))  
  putStrLn $ "bitLength 1 = " ++ (show $ bitLength (fromInteger 1 :: Number))  
  putStrLn $ "bitLength 2 = " ++ (show $ bitLength (fromInteger 2 :: Number))  
  putStrLn $ "bitLength 3 = " ++ (show $ bitLength (fromInteger 3 :: Number))  
  putStrLn $ "bitLength 4 = " ++ (show $ bitLength (fromInteger 4 :: Number))  
  putStrLn $ "bitLength 5 = " ++ (show $ bitLength (fromInteger 5 :: Number))  
  putStrLn $ "bitLength 6 = " ++ (show $ bitLength (fromInteger 6 :: Number))  
  putStrLn $ "bitLength 7 = " ++ (show $ bitLength (fromInteger 7 :: Number))  
  putStrLn $ "bitLength 8 = " ++ (show $ bitLength (fromInteger 8 :: Number))  
  


testEntropy :: IO ()
testEntropy = do
  bytes <- getEntropy 32 -- getEntropy :: Int -> IO BS.ByteString
  putStrLn $ show bytes

testCryptoRandomGen :: IO ()
testCryptoRandomGen = do
  g <- newGenIO :: IO SystemRandom    -- newGenIO :: CryptoRandomGen g => IO g
  case genBytes 32 g of
    Left e  -> putStrLn $ show e
    Right (bytes, g') -> putStrLn $ show bytes

  return ()
  
testRand :: IO ()
testRand = toIO $ do  -- inside the Rand monad
  bytes <- rand 32
  fromIO $ putStrLn $ "rand 32 = " ++ show bytes
  num <- random $ NumBits 0 :: Rand Number
  fromIO $ putStrLn $ "random 0 = " ++ show num
  num <- random $ NumBits 1 :: Rand Number
  fromIO $ putStrLn $ "random 1 = " ++ show num
  num <- random $ NumBits 2 :: Rand Number
  fromIO $ putStrLn $ "random 2 = " ++ show num
  num <- random $ NumBits 3 :: Rand Number
  fromIO $ putStrLn $ "random 3 = " ++ show num
  num <- random $ NumBits 4 :: Rand Number
  fromIO $ putStrLn $ "random 4 = " ++ show num
  num <- random $ NumBits 8 :: Rand Number
  fromIO $ putStrLn $ "random 8 = " ++ show num



testBinary :: IO ()
testBinary = do
  let x = 0xfffefdfcfbfaf9f8f7 :: Integer
  print x
  let bytes = encode x
  print bytes
  print $ BS.length bytes
  print $ (fromInteger x :: Word8)
  
  return ()

main :: IO ()
main = do
  testWord8
  testByteString
  testEntropy 
  testCryptoRandomGen
  testBinary
  testNumber
  testRand
  


