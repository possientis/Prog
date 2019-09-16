data Vect : Nat -> Type -> Type where
  Nil  : Vect Z a
  (::) : a -> Vect n a -> Vect (S n) a

data EqNat : (num1 : Nat) -> (num2:Nat) -> Type where
  Same : (num : Nat) -> EqNat num num

eqS :  {num1 : Nat} 
    -> {num2 : Nat} 
    -> (p : EqNat num1 num2) 
    -> EqNat (S num1) (S num2)
eqS (Same num) = Same (S num)

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat Z Z          = Just $ Same 0
checkEqNat Z (S k)      = Nothing 
checkEqNat (S k) Z      = Nothing
checkEqNat (S k) (S j)  = case checkEqNat k j of
  Nothing   => Nothing
  (Just p)  => Just $ eqS p


exactLength : (len : Nat) -> (input : Vect n a) -> Maybe (Vect len a)
exactLength {n} len input = case checkEqNat n len of
  Nothing         => Nothing
  Just (Same k)   => Just input
