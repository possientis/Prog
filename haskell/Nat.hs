import Control.Monad
import System.Directory

data Nat = Zero | Suc Nat deriving (Show)

(£) :: Nat -> Nat -> Nat
x £ Zero = x
x £ (Suc y) = Suc (x £ y)

zero = Zero
one = Suc Zero
two = Suc one
three = Suc two
four = Suc three
five = Suc four
six = Suc five
seven = Suc six
eight = Suc seven
nine = Suc eight
ten = Suc nine

p :: Nat -> Bool
p Zero = True
p (Suc n) | p n = True

toInt :: Nat -> Int
toInt Zero = 0
toInt (Suc n) = toInt n + 1

show :: Nat -> String
show n = Prelude.show (toInt n)


