import Test_Abstract
import Rand
import Number
import Data.ByteString

main :: IO ()
main = toIO run

run :: Rand ()
run = do
  logMessage "Number unit test running ..."
  checkZero
  checkOne
  checkFromBytes
  checkRandom
  checkSign
  checkToBytes
  checkAdd
  checkMul
  checkShow
  checkCompareTo
  checkHashCode
  checkNumberEquals
  checkFromInteger
  checkToInteger
  checkBitLength

signedRandom :: NumBits -> Rand Number
signedRandom n = do
  x     <- random n 
  flip  <- random (NumBits 1) :: Rand Number
  if flip == one
    then return $ negate x
    else return x
{-
testSignedRandom :: IO ()
testSignedRandom = toIO $ do
  x <- signedRandom (NumBits 256)
  fromIO $ putStrLn $ show x
-}

checkZero :: Rand ()
checkZero = do
  x <- random (NumBits 256) :: Rand Number
  let y = zero + x
  let z = x + zero
  checkEquals x y "checkZero.1"
  checkEquals x z "checkZero.2"


checkOne :: Rand ()
checkOne = do
  x <- random (NumBits 256) :: Rand Number
  let y = one * x
  let z = x * one
  checkEquals x y "checkOne.1"
  checkEquals x z "checkOne.2"
   
checkFromBytes :: Rand ()
checkFromBytes = do
  -- empty array
  let b0 = pack []
  x <- fromBytes (Sign 1) b0 :: Rand Number
  checkEquals x zero "checkFromBytes.1"
  x <- fromBytes (Sign (-1)) b0 :: Rand Number
  checkEquals x zero "checkFromBytes.2"
  x <- fromBytes (Sign 0) b0 :: Rand Number
  checkEquals x zero "checkFromBytes.3"
  let action = fromBytes (Sign 2) b0 :: Rand Number
  checkException action "InvalidArgument" "checkFromBytes.4"
  let action = fromBytes (Sign (-2)) b0 :: Rand Number
  checkException action "InvalidArgument" "checkFromBytes.5"

  -- single 0x00 byte
  let b1 = pack [0x00]
  x <- fromBytes (Sign 1) b1 :: Rand Number
  checkEquals x zero "checkFromBytes.6"
  x <- fromBytes (Sign (-1)) b1 :: Rand Number
  checkEquals x zero "checkFromBytes.7"
  x <- fromBytes (Sign 0) b1 :: Rand Number
  checkEquals x zero "checkFromBytes.8"
  let action = fromBytes (Sign 2) b1 :: Rand Number
  checkException action "InvalidArgument" "checkFromBytes.9"
  let action = fromBytes (Sign (-2)) b1 :: Rand Number
  checkException action "InvalidArgument" "checkFromBytes.10"
  
  -- two 0x00 bytes
  let b2 = pack [0x00, 0x00]
  x <- fromBytes (Sign 1) b2 :: Rand Number
  checkEquals x zero "checkFromBytes.11"
  x <- fromBytes (Sign (-1)) b2 :: Rand Number
  checkEquals x zero "checkFromBytes.12"
  x <- fromBytes (Sign 0) b2 :: Rand Number
  checkEquals x zero "checkFromBytes.13"
  let action = fromBytes (Sign 2) b2 :: Rand Number
  checkException action "InvalidArgument" "checkFromBytes.14"
  let action = fromBytes (Sign (-2)) b2 :: Rand Number
  checkException action "InvalidArgument" "checkFromBytes.15"
  
  -- single 0x01 bytes
  let b3 = pack [0x01]
  x <- fromBytes (Sign 1) b3 :: Rand Number
  checkEquals x one "checkFromBytes.16"
  let action = fromBytes (Sign 0) b3 :: Rand Number
  checkException action "InvalidArgument" "checkFromBytes.17"

  -- x + (-x) = 0
  b4 <- getRandomBytes 32
  x <- fromBytes (Sign 1) b4    :: Rand Number
  y <- fromBytes (Sign (-1)) b4 :: Rand Number
  checkEquals (x + y) zero "checkFromBytes.18"

  -- multiplying by -1
  z <- fromBytes (Sign (-1)) b3 -- (-1)
  checkEquals (x * z) y "checkFromBytes.19"

  -- padding with 0x00 bytes
  b5 <- getRandomBytes 28
  x <- fromBytes (Sign 1) b5    :: Rand Number
  y <- fromBytes (Sign (-1)) b5 :: Rand Number
  let b6 = pack $ 0:0:0:0:(unpack b5)
  z <- fromBytes (Sign 1) b6
  checkEquals x z "checkfromBytes.20"
  z <- fromBytes (Sign (-1)) b6
  checkEquals y z "checkfromBytes.21"

  -- actual replication
  
  
   
  return ()


checkRandom :: Rand ()
checkRandom = return () -- TODO

checkSign :: Rand ()
checkSign = return () -- TODO

checkToBytes :: Rand ()
checkToBytes = return () -- TODO

checkAdd :: Rand ()
checkAdd = return () -- TODO

checkMul :: Rand ()
checkMul = return () -- TODO

checkShow :: Rand ()
checkShow = return () -- TODO

checkCompareTo :: Rand ()
checkCompareTo = return () -- TODO

checkHashCode :: Rand ()
checkHashCode = return () -- TODO

checkNumberEquals :: Rand ()
checkNumberEquals = return () -- TODO

checkFromInteger :: Rand ()
checkFromInteger = return () -- TODO

checkToInteger :: Rand ()
checkToInteger = return () -- TODO

checkBitLength :: Rand ()
checkBitLength = return () -- TODO

