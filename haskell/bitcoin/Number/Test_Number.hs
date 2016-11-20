import Test_Abstract
import Rand
import Number
import Data.ByteString hiding (putStrLn)
import Data.Word
import Data.Bits
import Prelude hiding (foldl, length, replicate, head, init, last)

main :: IO ()
main = toIO run

run :: Rand ()
run = do
  logMessage "Number unit test running ..."
  checkZero
  checkOne
  checkFromBytes
--  checkRandom
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
  b7 <- getRandomBytes 32
  _255 <- fromBytes (Sign 1) (pack [0xff]) :: Rand Number
  let _256 = _255 + one
  x <- fromBytes (Sign 1) b7      :: Rand Number
  y <- fromBytes (Sign (-1)) b7   :: Rand Number

  
  let op sig acc byte = do                    -- operator needed for foldl
        a <- acc                              :: Rand Number
        b <- fromBytes sig (pack [byte])      :: Rand Number
        return $ _256 * a + b                 :: Rand Number

  z <- foldl (op (Sign 1)) (return zero) b7     -- foldl from Data.ByteString
  checkEquals x z "checkFromBytes.22"

  z <- foldl (op (Sign (-1))) (return zero) b7  -- foldl from Data.ByteString
  checkEquals y z "checkFromBytes.23"

  -- using toBytes and sign
  b8 <- getRandomBytes 32
  x <- fromBytes (Sign 1) b8    :: Rand Number
  y <- fromBytes (Sign (-1)) b8 :: Rand Number
  
  checkEquals (sign x)   1  "checkFromBytes.24"           -- sign :: a -> Int
  checkEquals (sign y) (-1) "checkFromBytes.25"

  checkEquals (signum x) one          "checkFromBytes.26" -- signum :: a -> a
  checkEquals (signum y) (negate one) "checkFromBytes.27" 

  b9  <- toBytes x (NumBytes 32)
  b10 <- toBytes y (NumBytes 32) 

  checkEquals b8 b9   "checkFromBytes.28"
  checkEquals b8 b10  "checkFromBytes.29"

checkSign :: Rand ()
checkSign = do
  checkEquals (sign (zero :: Number)) 0 "checkSign.1"
  checkEquals (signum (zero :: Number)) zero "checkSign.2"
  b <- getRandomBytes 32
  x <- fromBytes (Sign 1) b     :: Rand Number
  y <- fromBytes (Sign (-1)) b  :: Rand Number

  checkEquals (sign x)   1  "checkSign.3"
  checkEquals (sign y) (-1) "checkSign.4"

  checkEquals (signum x) one          "checkSign.5"
  checkEquals (signum y) (negate one) "checkSign.6"


checkToBytes :: Rand ()
checkToBytes = do

  -- zero
  bytes <- toBytes (zero :: Number) (NumBytes 0)
  checkEquals (length bytes) 0 "checkToBytes.1"

  bytes <- toBytes (zero :: Number) (NumBytes 32)
  checkEquals (length bytes) 32 "checkToBytes.2"

  checkEquals bytes (replicate 32 0x00) "checkToBytes.3" 

  -- one
  let action = toBytes (one :: Number) (NumBytes 0)
  checkException action "InvalidArgument" "checkToBytes.4"
  
  bytes <- toBytes (one :: Number) (NumBytes 1)
  checkEquals (length bytes) 1 "checkToBytes.5"
  checkEquals (head bytes) 0x01 "checkToBytes.6"
  
  bytes <- toBytes (negate one :: Number) (NumBytes 1)
  checkEquals (length bytes) 1 "checkToBytes.7"
  checkEquals (head bytes) 0x01 "checkToBytes.8"

  bytes <- toBytes (one :: Number) (NumBytes 32)
  checkEquals (length bytes) 32 "checkToBytes.9"
  checkEquals (last bytes) 0x01 "checkToBytes.10"
  checkEquals (init bytes) (replicate 31 0x00) "checkToBytes.11"  -- big-endian

  -- random
  x <- random (NumBits 256) :: Rand Number
  let y = negate x
  bytes <- toBytes x (NumBytes 32)
  z <- fromBytes (Sign 1) bytes
  checkEquals x z "checkToBytes.12"
  z <- fromBytes (Sign (-1)) bytes
  checkEquals y z "checkToBytes.13"
  bytes <- toBytes y (NumBytes 32)
  z <- fromBytes (Sign 1) bytes
  checkEquals x z "checkToBytes.14"
  z <- fromBytes (Sign (-1)) bytes
  checkEquals y z "checkToBytes.15"


checkRandom :: Rand ()
checkRandom = do
  -- checking a random generator should be far more involved
  -- than anything done here
  x <- random (NumBits 0) :: Rand Number
  checkEquals x zero "checkRandom.1"

  x <- random (NumBits 1) :: Rand Number  -- single bit
  checkCondition (x == zero || x == one) "checkRandom.2"

  x <- random (NumBits 256) :: Rand Number
  checkEquals (sign x) 1 "checkRandom.3"
  
  -- selecting random positive integer with 256 bits
  -- selecting a random byte of this integer and a random bit of this byte
  -- repeating the process 10000 times and counting the number of set bits

  let go acc i =
        if i <= (0 :: Int)                            -- loop terminates
          then return acc :: Rand Int
          else do
            x <- random (NumBits 256) :: Rand Number  -- random 256 bits
            bytes <- toBytes x (NumBytes 32)          -- getting bytes
            y <- random (NumBits 5)   :: Rand Number  -- selecting byte 0 to 31
            b <- toBytes y (NumBytes 1)
            let j =  fromIntegral $ head b :: Int
            let test = index bytes j  :: Word8        -- retrieving bytes[j]
            z <- random (NumBits 3)   :: Rand Number  -- selecting bit 0..7 
            c <- toBytes z (NumBytes 1)
            let bit = fromIntegral $ head c :: Int
            let add = if testBit test bit then 1 else 0 
            go (acc + add) (i - 1)
   
  count <- go 0 10000
  
  checkCondition (count > 4800) "checkRandom.4"
  checkCondition (count < 5200) "checkRandom.5"

  return ()


checkAdd :: Rand ()
checkAdd = do
  x <- signedRandom (NumBits 256)
  y <- signedRandom (NumBits 256)
  z <- signedRandom (NumBits 256)

  -- x + 0 = x
  checkEquals (x + zero) x "checkAdd.1"

  -- 0 + x = x
  checkEquals (zero + x) x "checkAdd.2"

  -- x + (-x) = 0
  checkEquals (x + (negate x)) zero "checkAdd.3"

  -- (-x) + x = 0
  checkEquals (negate x + x) zero "checkAdd.4"

  -- x + y = y + x
  checkEquals (x + y) (y + x) "checkAdd.5"

  -- (x + y) + z = x + (y + z)
  checkEquals ((x + y) + z) (x + (y + z)) "checkAdd.6"

  -- actual check of x + y
  let n = toInteger x
  let m = toInteger y
  let sum = n + m
  let check = fromInteger sum
  checkEquals check (x + y) "checkAdd.7"


checkMul :: Rand ()
checkMul = do

  x <- signedRandom (NumBits 256)
  y <- signedRandom (NumBits 256)
  z <- signedRandom (NumBits 256)

  -- x * 0 = 0
  checkEquals (x * zero) zero "checkMul.1"

  -- 0 * x = 0
  checkEquals (zero * x) zero "checkMul.2"

  -- x * 1 = x
  checkEquals (x * one) x "checkMul.3"

  -- 1 * x = x
  checkEquals (one * x) x "checkMul.4"

  -- (-x) * (-y) = x * y
  checkEquals (negate x * negate y) (x * y) "checkMul.5"

  -- x * y = y * x
  checkEquals (x * y) (y * x) "checkMul.6"

  -- (x * y) * z = x * (y * z)
  checkEquals ((x * y) * z) (x * (y * z)) "checkMul.7"

  -- (x + y) * z = (x * z) + (y * z)
  checkEquals ((x + y) * z) ((x * z) + (y * z)) "checkMul.8"

  -- actual check of x * y
  let n = toInteger x
  let m = toInteger y
  let prod = n * m
  let check = fromInteger prod
  checkEquals check (x * y) "checkMul.9" 



checkShow :: Rand ()
checkShow = do
  
  -- zero
  checkEquals (show (zero :: Number)) "0" "checkShow.1"

  -- one
  checkEquals (show (one :: Number)) "1" "checkShow.2"

  -- minus one
  checkEquals (show $ (negate one :: Number)) "-1" "checkShow.3"

  -- random positive
  x <- random (NumBits 256) :: Rand Number
  checkEquals (show x) (show $ toInteger x) "checkShow.4"

  

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
