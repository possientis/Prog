type MyString = [Char]

f :: MyString -> Int
f[] = 0
f (x:xs) = 1 + f xs

type Pos = (Int,Int)

origin :: Pos
origin = (0,0)

left :: Pos -> Pos
left (x,y) = (x-1,y)

g :: (Int,Int) -> (Int,Int)
g (x,y) = (x-1,y)

type Pair a = (a,a)
mult :: Pair Int -> Int
mult (m,n) = m*n

copy :: a -> Pair a
copy x = (x,x)

data MyBool = MyFalse | MyTrue
h :: () -> MyBool
h () = MyFalse

data Answer = Yes | No | Unknown

answers :: [Answer]
answers = [Yes,No,Unknown]
flip :: Answer -> Answer
flip Yes = No
flip No = Yes
flip Unknown = Unknown

data Shape = Circle Float | Rect Float Float

square :: Float -> Shape
square n = Rect n n

area :: Shape -> Float
area (Circle r) = pi * r^2
area (Rect x y) = x * y

myShape = Circle 5.0

safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:xs) = Just x

data Nat = Zero | Succ Nat

nat2int :: Nat -> Int
nat2int Zero = 0
nat2int (Succ n) = 1 + nat2int n

int2nat :: Int -> Nat
int2nat 0 = Zero
int2nat n = Succ (int2nat (n-1))

add :: Nat -> Nat -> Nat
add m n = int2nat(nat2int m + nat2int n)

myAdd :: Nat -> Nat -> Nat
myAdd Zero n = n
myAdd (Succ m) n = Succ (myAdd m n)

yourAdd :: Int -> Int -> Int
yourAdd m n = nat2int(myAdd (int2nat m) (int2nat n))

data Expr =   Val Int
            | Add Expr Expr
            | Mul Expr Expr
myExpr = Add (Val 1) (Mul (Val 2) (Val 3))

size :: Expr -> Int
size (Val n) = 1
size (Add x y) = size x + size y
size (Mul x y) = size x + size y

eval :: Expr -> Int
eval (Val n) = n
eval (Add x y) = eval x + eval y
eval (Mul x y) = eval x * eval y

data Tree = Leaf Int | Node Tree Int Tree

myTree = Node (Node (Leaf 1) 3 (Leaf 4))
         5
         (Node (Leaf 6) 7 (Leaf 9))

occurs :: Int -> Tree -> Bool
occurs m (Leaf n) = (m == n)
occurs m (Node l n r) = (m == n)
                              || occurs m l
                              || occurs m r

flatten :: Tree -> [Int]
flatten (Leaf n) = [n]
flatten (Node l n r) = flatten l
                     ++ [n]
                     ++ flatten r

