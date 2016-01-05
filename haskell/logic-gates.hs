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
makeGate f [] _ = []
makeGate f [] _ = []
makeGate f (x:xs) (y:ys) = toInt (f (toBool x) (toBool y)) : makeGate f xs ys


