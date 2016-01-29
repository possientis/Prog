f n = n:ns where ns = if even n then  f (div n 2) else f (3 * n +1)

g (1:xs) = [1]
g (x:xs) = x : g xs

h n = g (f n)

k n = length (h n)

list n = (n , (k n)) : list (n + 1)


maxi [] a = a
maxi ((n,m):xs) a = if m > snd(a) then maxi xs (n,m) else maxi xs a

q n = maxi (take n (list 1)) (0,0)


