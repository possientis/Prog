myDrop n xs | n <= 0  = xs
myDrop _ []           = []
myDrop n (x:xs)       = myDrop (n - 1) xs 
