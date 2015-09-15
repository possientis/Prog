isZero :: Int -> Bool
isZero n | (n == 0) = True
isZero n | (n /= 0) = False


data Nat = Zero | Succ Nat

add :: Nat -> Nat -> Nat
add Zero n = n
add (Succ m) n = Succ(add m n)

toInt :: Nat -> Int
toInt Zero = 0
toInt (Succ n) = 1 + toInt n

toNat :: Int -> Nat
toNat 0 = Zero
toNat n = Succ (toNat (n-1))



loop :: ([a],[a])-> ([a],[a])
loop ([],xs) = ([],xs)
loop (y:ys,xs) = loop (ys, y:xs)


myReverse :: [a] -> [a]
myReverse xs = snd (loop (xs,[]))

myFoldr cons nil [] = nil
myFoldr cons nil (x:xs) = cons x (myFoldr cons nil xs)

--yourFolder cons nil = f where f = \xs ->
--  case xs of
--  {
--  [] -> nil
--  , (y:ys) -> cons y (f ys)
--  }

fix g x = g (fix g x)
