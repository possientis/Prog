power :: Integer -> Integer
power 0 = 1
power n = 2^(power (n-1))
