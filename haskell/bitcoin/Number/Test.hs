import Number
import Control.Monad.CryptoRandom
import System.Entropy
import qualified Data.ByteString as BS
import Data.Word
import Data.Bits 

type ByteString = BS.ByteString

x = zero :: Number
y = one :: Number
z = fromInteger 23 :: Number
t = fromInteger $ -3 :: Number

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

testByteString :: IO ()
testByteString = do
  putStrLn $ "empty = " ++ show BS.empty
  putStrLn $ "singleton 255 = " ++ (show $ BS.singleton $ fromInteger 255)
  

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
  putStrLn $ "signum t = " ++ (show $ signum t)
  putStrLn $ "signum x = " ++ (show $ signum x)
  putStrLn $ "toInteger z = " ++ (show $ toInteger z)
  putStrLn $ "hash x = " ++ (show $ hash x)
  putStrLn $ "hash y = " ++ (show $ hash y)
  putStrLn $ "hash z = " ++ (show $ hash z)
  putStrLn $ "hash t = " ++ (show $ hash t)


main :: IO ()
main = do
  testByteString
  


