type Signal = [Int]
notGate :: Signal -> Signal
notGate [] = []
notGate (x:xs) = (toInt.not.toBool) x : notGate xs

toBool :: Int -> Bool
toBool n = if n == 0 then False else True

toInt  :: Bool -> Int
toInt True = 1
toInt False = 0

makeGate :: (Bool -> Bool -> Bool) -> Signal -> Signal -> Signal
makeGate f [] _   = []
makeGate f _  []  = []
makeGate f (x:xs) (y:ys) = toInt (f (toBool x) (toBool y)) : makeGate f xs ys

orGate :: Signal -> Signal -> Signal
orGate = makeGate (\x -> \y -> or [x,y])

andGate :: Signal -> Signal -> Signal
andGate = makeGate (\x -> \y -> and [x,y])

nand :: Bool -> Bool -> Bool
nand x y = not (and [x,y])
nandGate = makeGate nand

nor :: Bool -> Bool -> Bool
nor x y = not (or [x,y])
norGate = makeGate nor

xor :: Bool -> Bool -> Bool
xor x y = (x /= y)
xorGate = makeGate xor

delayGate :: Signal -> Signal
delayGate xs = 0:xs

fullAdder :: Signal -> Signal -> Signal -> (Signal,Signal)
fullAdder in1 in2 cin = (sum,cout) where
  sum   = xorGate cin (xorGate in1 in2)
  cout  = orGate (andGate in1 in2) (orGate (andGate cin in1) (andGate cin in2))

rsLatch :: Signal -> Signal -> (Signal, Signal)
rsLatch inR inS = (a,b) where
  a = nandGate inS (delayGate b)
  b = nandGate inR (delayGate a)

simpleLatch :: Signal -> Signal -> Signal
simpleLatch assertWrite input = output where
  output = orGate (andGate input assertWrite)
                  (andGate (delayGate output) (notGate assertWrite))

simpleLatchTest = let
  assertWrite = [0,1,0,0,1,1,0,0,1,0,0,0,0,0,0,1,0,0,0,0]
  input       = [0,1,0,1,0,1,0,1,0,0,1,0,0,0,1,1,0,0,0,0]
  output      = simpleLatch assertWrite input
  in do
    putStrLn "Assert:"
    putStrLn (show assertWrite)
    putStrLn "Input:"
    putStrLn (show input)
    putStrLn "Output:"
    putStrLn (show output)
    


rsLatchTest = let
  inS   = [0,0,0,1,1,1,1,1,1,1,0,0,1,1,1,1,1,1,1,1]
  inR   = [0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,0,0,1,1,1]
  (a,b) = rsLatch inR inS
  in do
    putStrLn "Input:"
    putStrLn (show inS)
    putStrLn (show inR)
    putStrLn "Output:"
    putStrLn (show a)
    putStrLn (show b)


main = simpleLatchTest



