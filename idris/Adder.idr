AdderType : (numArgs : Nat) -> Type
AdderType Z     = Int
AdderType (S k) = (next : Int) -> AdderType k


adder : (numArgs : Nat) -> (acc : Int) -> AdderType numArgs
adder Z     acc = acc
adder (S k) acc = \next => adder k (acc + next)


AdderType' : (numArgs : Nat) -> Type -> Type
AdderType' Z a     = a
AdderType' (S k) a = a -> AdderType' k a

adder' : (Num a) => (numArgs : Nat) -> a -> AdderType' numArgs a
adder' Z acc     = acc
adder' (S k) acc = \next => adder' k (acc + next) 


main : IO ()
main = do
  printLn $ adder' 3 10 20 35 45
