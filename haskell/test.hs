-- not idiomatic
myDrop n xs = if n <= 0 || null xs
              then xs
              else myDrop (n - 1) (tail xs)
isOdd n = mod n 2 == 1


