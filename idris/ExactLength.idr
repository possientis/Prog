data Vect : Nat -> Type -> Type where
  Nil  : Vect Z a
  (::) : a -> Vect n a -> Vect (S n) a


exactLength : (len : Nat) -> (input : Vect n a) -> Maybe (Vect len a)
exactLength {n} len input = case n == len of
  False => Nothing
  True  => Just ?rest
