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


