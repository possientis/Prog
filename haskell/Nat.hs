data Nat = Zero | Succ Nat

data Zero     -- Zero is a type without constructor
data Succ n   -- Succ is a parameterized type without constructor 

type Three = Succ (Succ (Succ Zero))

class Even n  where isEven :: n
class Odd n   where isOdd :: n

instance Even Zero
instance Odd n => Even (Succ n)
instance Even n => Odd (Succ n)



