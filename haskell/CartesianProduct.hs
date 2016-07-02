comprehensive xs ys = [(x,y) | x <- xs, y <- ys]

test1 = comprehensive [1,2,3] [4,5,6] -- [(1,4),(1,5),(1,6),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6)]

monadic xs ys = do { x <- xs; y <- ys; return (x,y) }

test2 = monadic [1,2,3] [4,5,6] -- [(1,4),(1,5),(1,6),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6)]


test3 xs = do { x <- xs; return x }
test4 = test3 [1,2,3] -- [1,2,3]


