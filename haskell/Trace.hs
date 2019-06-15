import Debug.Trace

x .: xs = trace ":" (x : xs)
nil     = trace "." []
num x   = trace "0" x
list    = foldr (.:) nil (map num [1..10])

main = print $ sum (take 2 (drop 3 list))

