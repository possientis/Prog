data Vect : Nat -> Type -> Type where
  Nil  : Vect Z a
  (::) : a -> Vect n a -> Vect (S n) a


exactLength : (len : Nat) -> (input : Vect n a) -> Maybe (Vect len a)
exactLength len input = ?exactLength_rhs
