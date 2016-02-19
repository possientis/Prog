import Data.List

-- length
-- null
-- head
-- tail
-- last [a] -> a

-- init [a] -> [a] (removes last element)
l1 = init [1,2,3,4,5] -- [1,2,3,4]

-- (++)

-- concat [[a]] -> [a]
l2 = concat [[1,2,3],[4,5,6]] -- [1,2,3,4,5,6]

-- reverse

-- or [Bool] -> Bool
-- and [Bool] -> Bool
-- generalization of (||) and (&&)
--

-- all (a -> Bool) -> [a] -> Bool
l3 = all odd [1,3,5] -- True

-- any (a -> Bool) -> [a] -> Bool
l4 = any even [3,1,4,1,5,9,2,6,5] -- True


-- take
-- drop


--splitAt Int -> [a] -> ([a],[a])
tuple1 = splitAt 3 "foobar" -- ("foo","bar")

-- takeWhile (a -> Bool) -> [a] -> [a]
l5 = takeWhile odd [1,3,5,6,8,9,11] -- [1,3,5]

-- dropWhile (a -> Bool) -> [a] -> [a]
l6 = dropWhile even [2,4,6,7,9,10,12] -- [7,9,10,12]

-- span (a -> Bool) -> [a] -> ([a],[a])
tuple2 = span even [2,4,6,7,9,10,11] -- ([2,4,6], [7,9,10,11])

-- break (a -> Bool) -> [a] -> ([a],[a])
tuple3 = break even [1,3,5,6,8,9,10] -- ([1,3,5], [6,8,9,10])



-- elem (Eq a) => a -> [a] -> Bool
-- notElem
-- filter (a -> Bool) -> [a] -> [a]
--
-- isPrefixOf (Eq a) => [a] -> [a] -> Bool
-- isSuffixOf (Eq a) => [a] -> [a] -> Bool
-- isInfixOf  (Eq a) => [a] -> [a] -> Bool
--
-- zip [a] -> [b] -> [(a,b)]
-- zipWith (a -> b -> c) -> [a] -> [b] -> [c]
-- cannot use 'map' here as you would in Lisp
l7 = zipWith (+) [1,2,3] [4,5,6]  -- [5,7,9]

-- zip3, zipWith3, zip7, zipWith7 etc.
--
-- lines [Char] -> [[Char]] (i.e. String -> [String])
l8 = lines "foo\nbar" -- ["foo","bar"]

-- unlines [[Char]] -> [Char] (i.e. [String] -> String)
l9 = unlines ["foo","bar"]  -- "foo\n\bar\n"








