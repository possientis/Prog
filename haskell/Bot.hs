f :: (Int,Int) -> Bool
f (_,_)  = True

g :: (Int,Int) -> Bool
g ~(_,_) = True

x = error "nope" :: Int
y = (x,x) :: (Int, Int)
y'= error "nope" :: (Int, Int)

fact :: Int -> Int
fact 0     = 1
fact (n+1) = (n+1) * fact n

