newtype DiffList a = DL ([a]->[a])

nil :: DiffList a
nil = DL (\ys -> ys)

isNil :: Eq a => DiffList a -> Bool
isNil (DL f) = f [] == []

cons :: a -> DiffList a -> DiffList a
cons x (DL f) = DL (\ys -> x:(f ys))

car :: DiffList a -> a
car (DL f) = head (f [])

cdr :: DiffList a -> DiffList a
cdr (DL f) = DL (\ys -> tail (f ys))

diff :: [a] -> DiffList a
diff [] = nil
diff (x:xs) = cons x (diff xs)

list :: DiffList a -> [a]
list (DL f) = f []

append :: DiffList a -> DiffList a -> DiffList a
append (DL g) (DL f) = DL (\zs -> g (f zs))

s :: DiffList Int
s = diff [0,1,2,3,4,5,6,7,8,9]

t :: DiffList Int
t = diff [10,11,12,13,14,15]

u :: DiffList Int
u = append s t


