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
{-
  benchmark (return (zero :: Number)) "zero" 1000000
  benchmark (return (0 :: Integer)) "zero*" 1000000
-}
  benchmark (return ()) "return" 1000000


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

benchToBytes :: Rand()
benchToBytes = return () -- TODO

benchAdd :: Rand()
benchAdd = return () -- TODO

benchMul :: Rand()
benchMul = return () -- TODO

benchShow :: Rand()
benchShow = return () -- TODO

benchRandom :: Rand()
benchRandom = return () -- TODO

benchSign :: Rand()
benchSign = return () -- TODO

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

















