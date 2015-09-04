myAbs :: Int -> Int
myAbs n = if n >= 0 then n else -n

sigNum :: Int -> Int
sigNum n =  if n < 0 then -1 else
            if n == 0 then 0 else 1

yourAbs :: Int -> Int
yourAbs n | n>= 0     = n
          | otherwise = -n

mySig n | n < 0       = -1
        | n == 0      =  0
        | otherwise   =  1

(£) :: Bool -> Bool -> Bool
True £ True = True
_ £ _ = False

myHead (a:_) = a
myTail (_:a) = a

myConst x = \_ -> x

odds n = map (\x -> 2 * x + 1) [0..n-1]
myOdds n = map f [0..n-1] where f x = 2 * x + 1

($$$) :: Int -> Int -> Int
x $$$ y = x + y

