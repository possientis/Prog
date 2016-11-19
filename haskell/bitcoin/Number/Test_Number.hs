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

