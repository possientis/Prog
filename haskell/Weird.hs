data Weird a b  = First a
                | Second b
                | Third [(a,b)]
                | Fourth (Weird a b)

weirdMap :: (a -> c) -> (b -> d) -> Weird a b -> Weird c d
weirdMap fa fb = g
  where
    g (First x)   = First (fa x)
    g (Second y)  = Second (fb y)
    g (Third zs)  = Third [ (fa x, fb y) | (x,y) <- zs ]
    g (Fourth w)  = Fourth (g w)
    
weirdFold :: (a -> c) -> (b -> c) -> ([(a,b)] -> c)-> (c -> c) -> Weird a b -> c
weirdFold f1 f2 f3 f4 = g 
  where
    g (First x)   = f1 x
    g (Second y)  = f2 y
    g (Third z)   = f3 z
    g (Fourth w)  = f4 (g w)


data List a   = Nil | Cons a (List a)

listFoldr :: (a -> b -> b) -> b -> List a -> b
listFoldr fCons fNil = g 
  where
    g Nil         = fNil
    g (Cons x xs) = fCons x (g xs)
