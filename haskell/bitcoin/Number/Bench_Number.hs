import Bench_Abstract
import Rand
import Number

main :: IO ()
main = toIO run

run :: Rand ()
run = do
  logMessage "Number benchmark running ..."

  let all = True

  benchFromBytes
  benchToBytes
  benchAdd
  benchMul
  benchShow
  benchRandom

  if all then do
    liftIO benchZero
    benchOne
    benchSign
    benchCompareTo
    benchHash
    benchNumberEquals
    benchFromInteger
    benchToInteger
    benchBitLength
  else
    return ()

benchZero :: IO ()
benchZero = do 
  benchmark (return (zero :: Number)) "zero" 1000000
  benchmark (return (0 :: Integer)) "zero*" 1000000


benchOne :: Rand ()
benchOne = do
  benchmark (return (one :: Number)) "one" 1000000
  benchmark (return (1 :: Integer)) "one*" 1000000


benchFromBytes :: Rand ()
benchFromBytes = do
  bytes <- getRandomBytes 32
  benchmark ( do 
    fromBytes (Sign 1)  bytes :: Rand Number
    fromBytes (Sign (-1)) bytes :: Rand Number
    ) "fromBytes" 1000000

benchToBytes :: Rand ()
benchToBytes = do
  x <- random (NumBits 256) :: Rand Number
  let y = negate x
  let n = toInteger x
  let m = toInteger y 
  benchmark ( do
    toBytes x (NumBytes 32)
    toBytes y (NumBytes 32)
    ) "toBytes" 1000000



benchAdd :: Rand()
benchAdd = do
  x <- random (NumBits 256) :: Rand Number
  y <- negate <$> random (NumBits 256) :: Rand Number
  let n = toInteger x
  let m = toInteger y
  benchmark ((return $ x + y) >> (return $ y + x)) "add" 1000000
  benchmark ((return $ n + m) >> (return $ m + n)) "add*" 1000000

benchMul :: Rand()
benchMul = do 
  x <- random (NumBits 256) :: Rand Number
  y <- negate <$> random (NumBits 256) :: Rand Number
  let n = toInteger x
  let m = toInteger y
  benchmark ((return $ x * y) >> (return $ y * x)) "mul" 1000000
  benchmark ((return $ n * m) >> (return $ m * n)) "mul*" 1000000

  

benchShow :: Rand()
benchShow = do
  x <- random (NumBits 256) :: Rand Number
  y <- negate <$> random (NumBits 256) :: Rand Number
  let n = toInteger x
  let m = toInteger y
  benchmark ((return $ show x) >> (return $ show y)) "show (10k)" 10000
  benchmark ((return $ show n) >> (return $ show m)) "show* (10k)" 10000


benchRandom :: Rand()
benchRandom = benchmark (random (NumBits 256) :: Rand Number) "random (10k)" 10000

benchSign :: Rand()
benchSign = do
  x <- random (NumBits 256) :: Rand Number
  y <- negate <$> random (NumBits 256) :: Rand Number
  let n = toInteger x
  let m = toInteger y
  benchmark ((return $ sign x) >> (return $ sign y)) "sign" 1000000
  benchmark ((return $ signum x) >> (return $ signum y)) "signum" 1000000
  benchmark ((return $ signum n) >> (return $ signum m)) "signum*" 1000000


benchCompareTo :: Rand()
benchCompareTo = return () -- TODO

benchHash :: Rand()
benchHash = return () -- TODO

benchNumberEquals :: Rand()
benchNumberEquals = return () -- TODO

benchFromInteger :: Rand()
benchFromInteger = return () -- TODO

benchToInteger :: Rand()
benchToInteger = return () -- TODO

benchBitLength :: Rand()
benchBitLength = return () -- TODO

















