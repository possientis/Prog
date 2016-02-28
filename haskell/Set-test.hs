import Set


func :: (Eq a) => a -> a -> Bool
func x y = (x == y)

testSet :: (Eq a, ISet a) => a -> a -> Bool
testSet x y = (x == y)
