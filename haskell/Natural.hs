module Natural(Nat) where -- only exporting type 'Nat'
-- type constructor 'MkNat' is not exported (private, encapsulated)

-- only one constructor with one argument
-- => can use 'newtype' keyword rather than 'data'
-- probably more efficient way to achieving boxing
newtype Nat = MkNat Integer

-- Abstract data type internal representation need to fullfil invariant
invariant :: Nat -> Bool
invariant (MkNat x) = x >= 0


-- implementing Eq interface (type class)
instance Eq Nat where
  MkNat x == MkNat y = x == y

-- implementing Ord interface (need to focus on <=)
instance Ord Nat where
  MkNat x <= MkNat y = x <= y

-- implementing Show interface
instance Show Nat where
  show (MkNat x) = show x

-- implementing Num interface
instance Num Nat where
  MkNat x + MkNat y = MkNat (x + y)
  MkNat x * MkNat y = MkNat (x * y)
  fromInteger x | x >= 0    = MkNat x
                | otherwise = error(show x ++ " is negative") -- type Nat???
  abs x = x
  signum x = 1

-- implementing Enum interface  (iterators, IEnumerable...)
instance Enum Nat where -- 1-1 correspondance with Int
  -- toEnum
  -- fromEnum
  -- ,,, => succ, pred, enumFrom, enumFromTo, ...


