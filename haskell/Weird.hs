data Weird a b  = First a
                | Second b
                | Third [(a,b)]
                | Fourth (Weird a b)

weirdMap :: (a -> c) -> (b -> d) -> Weird a b -> Weird c d
weirdMap fa fb = g
  where
    g (First x)   = First (fa x)
    g (Second y)  = Second (fb y)
    g (Third zs)  = Third (h zs)
    g (Fourth w)  = Fourth (g w)
    h []          = []
    h ((x,y):zs)  = (fa x, fb y):h zs
    
