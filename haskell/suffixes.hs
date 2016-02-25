import Data.List

t = tails "foobar"


suffixes :: [a] -> [[a]]
suffixes (x:xs) = (x:xs):suffixes xs -- this allocates new cons (x:xs)
suffixes _      = [[]]

suffixes' :: [a] -> [[a]]
-- as-pattern: 'bind the variable xs to the value that
-- matches the right side of the @ symbol
suffixes' xs@(_:xs') = xs:suffixes' xs' -- this does not allocates new cons
suffixes' _ = [[]]
